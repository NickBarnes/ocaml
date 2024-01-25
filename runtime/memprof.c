/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*            Jacques-Henri Jourdan, projet Gallium, INRIA Paris          */
/*                                                                        */
/*   Copyright 2016 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include <stdbool.h>
#include "caml/alloc.h"
#include "caml/fail.h"
#include "caml/memory.h"
#include "caml/memprof.h"
#include "caml/mlvalues.h"

/* type aliases for the hierarchy of structures for managing memprof status. */

typedef struct memprof_domain_s memprof_domain_s, *memprof_domain_t;
typedef struct memprof_thread_s memprof_thread_s, *memprof_thread_t;

/* Per-thread memprof state. */

struct memprof_thread_s {
  /* [suspended] is used for inhibiting memprof callbacks when
     a callback is running or when an uncaught exception handler is
     called. */
  bool suspended;

  /* TODO: More fields to add here */

  /* Per-domain memprof information */
  memprof_domain_t domain;

  /* Linked list of thread structures for this domain. Could use a
   * doubly-linked list for performance, but I haven't measured it. */
  memprof_thread_t next;
};

/* A memprof configuration is held in an object on the Caml heap, of
 * type Gc.Memprof.t. Here we define getter macros for each field, and
 * a setter macro for the status field (which is updated). */

#define CONFIG_FIELDS 9

#define CONFIG_FIELD_STATUS        0
#define CONFIG_FIELD_LAMBDA        1
#define CONFIG_FIELD_1LOG1ML       2
#define CONFIG_FIELD_FRAMES        3
#define CONFIG_FIELD_ALLOC_MINOR   4
#define CONFIG_FIELD_ALLOC_MAJOR   5
#define CONFIG_FIELD_PROMOTE       6
#define CONFIG_FIELD_DEALLOC_MINOR 7
#define CONFIG_FIELD_DEALLOC_MAJOR 8

#define CONFIG_FIELD_FIRST_CALLBACK CONFIG_FIELD_ALLOC_MINOR
#define CONFIG_FIELD_LAST_CALLBACK CONFIG_FIELD_DEALLOC_MAJOR

#define CONFIG_STATUS_RUNNING 0
#define CONFIG_STATUS_STOPPED 1
#define CONFIG_STATUS_DISCARDED 2

#define CONFIG_NONE Val_unit

#define Status(config)          Int_val(Field(config, CONFIG_FIELD_STATUS))
#define Running(config)          ((config != CONFIG_NONE) && \
                                  (Status(config) == CONFIG_STATUS_RUNNING))

/* The 'status' field is the only one we ever update. */

#define Set_status(config, stat) \
  Store_field(config, CONFIG_FIELD_STATUS, Val_int(stat))

/* lambda: the fraction of allocated words to sample 0 <= lambda <= 1 */
#define Lambda(config) \
  Double_val(Field(config, CONFIG_FIELD_LAMBDA))

/* 1/ln(1-lambda), pre-computed for use in the geometric RNG */
#define One_log1m_lambda(config) \
  Double_val(Field(config, CONFIG_FIELD_1LOG1ML))

/* The number of frames to record for each allocation site */
#define Callstack_size(config) \
  Int_val(Field(config, CONFIG_FIELD_FRAMES))

/* callbacks */
#define Alloc_minor(config)   Field(config, CONFIG_FIELD_ALLOC_MINOR)
#define Alloc_major(config)   Field(config, CONFIG_FIELD_ALLOC_MAJOR)
#define Promote(config)       Field(config, CONFIG_FIELD_PROMOTE)
#define Dealloc_minor(config) Field(config, CONFIG_FIELD_DEALLOC_MINOR)
#define Dealloc_major(config) Field(config, CONFIG_FIELD_DEALLOC_MAJOR)

/* Per-domain memprof state */

struct memprof_domain_s {
  /* The owning domain */
  caml_domain_state *caml_state;

  /* Linked list of threads in this domain */
  memprof_thread_t threads;

  /* The current thread's memprof state. Note that there may not be a
     "current thread". TODO: maybe this shouldn't be nullable.
     Nullability costs us some effort and may be meaningless. See call
     site of caml_memprof_leave_thread() in st_stubs.c. */
  memprof_thread_t current;

  /* The current profiling configuration for this domain. */
  value config;

  /* TODO: More fields to add here */
};

/* Return configuration for a domain. If it's been discarded (e.g. by
   another domain) then reset it to CONFIG_NONE and return that.
*/

static value domain_config(memprof_domain_t domain)
{
  value config = domain->config;
  if ((config != CONFIG_NONE) &&
      (Status(config) == CONFIG_STATUS_DISCARDED)) {
    config = domain->config = CONFIG_NONE;
  }
  return config;
}

/**** Create and destroy thread state structures ****/

static memprof_thread_t thread_create(memprof_domain_t domain)
{
  memprof_thread_t thread = caml_stat_alloc(sizeof(memprof_thread_s));
  if (!thread) {
    return NULL;
  }
  thread->suspended = false;

  /* attach to domain record */
  thread->domain = domain;
  thread->next = domain->threads;
  domain->threads = thread;

  return thread;
}

static void thread_destroy(memprof_thread_t thread)
{
  memprof_domain_t domain = thread->domain;

  if (domain->current == thread) {
    domain->current = NULL;
  }
  /* remove thread from the per-domain list. Could go faster if we
   * used a doubly-linked list, but that's premature optimisation
   * at this point. */
  memprof_thread_t *p = &domain->threads;
  while (*p != thread) {
    p = &(*p)->next;
  }

  *p = thread->next;

  caml_stat_free(thread);
}

/**** Create and destroy domain state structures ****/

static void domain_destroy(memprof_domain_t domain)
{
  memprof_thread_t thread = domain->threads;
  while (thread) {
    memprof_thread_t next = thread->next;
    thread_destroy(thread);
    thread = next;
  }

  caml_stat_free(domain);
}

static memprof_domain_t domain_create(caml_domain_state *caml_state)
{
  memprof_domain_t domain = caml_stat_alloc(sizeof(memprof_domain_s));
  if (!domain) {
    return NULL;
  }

  domain->caml_state = caml_state;
  domain->threads = NULL;
  domain->current = NULL;
  domain->config = CONFIG_NONE;

  /* create initial thread for domain */
  memprof_thread_t thread = thread_create(domain);
  if (thread) {
    domain->current = thread;
  } else {
    domain_destroy(domain);
    domain = NULL;
  }
  return domain;
}

/**** GC interface ****/

void caml_memprof_scan_roots(scanning_action f,
                             scanning_action_flags fflags,
                             void* fdata,
                             caml_domain_state *state,
                             _Bool young,
                             _Bool global)
{
  memprof_domain_t domain = state->memprof;

  f(fdata, domain->config, &domain->config);
}

void caml_memprof_after_minor_gc(caml_domain_state *state, _Bool global)
{
}

void caml_memprof_after_major_gc(caml_domain_state *state, _Bool global)
{
}

/**** Running callbacks ****/

value caml_memprof_run_callbacks_exn(void)
{
  return Val_unit;
}

/**** Interface to domain module ***/

void caml_memprof_new_domain(caml_domain_state *parent,
                             caml_domain_state *child)
{
  memprof_domain_t domain = domain_create(child);

  child->memprof = domain;
  /* domain inherits configuration from parent */
  if (domain && parent) {
    domain->config = parent->memprof->config;
  }
}

void caml_memprof_delete_domain(caml_domain_state *state)
{
  if (!state->memprof) {
    return;
  }
  domain_destroy(state->memprof);
  state->memprof = NULL;
}

/**** Interface with domain action-pending flag ****/

/* If profiling is active in the current domain, and we may have some
 * callbacks pending, set the action pending flag. */

static void set_action_pending_as_needed(memprof_domain_t domain)
{
  /* if (condition) caml_set_action_pending(domain->caml_state); */
}

/* Set the suspended flag on `domain` to `s`. */

static void update_suspended(memprof_domain_t domain, bool s)
{
  if (domain->current) {
    domain->current->suspended = s;
  }
  caml_memprof_renew_minor_sample(domain->caml_state);
  if (!s) set_action_pending_as_needed(domain);
}

/* Set the suspended flag on the current domain to `s`. */

void caml_memprof_update_suspended(bool s) {
  update_suspended(Caml_state->memprof, s);
}

/**** Sampling procedures ****/

Caml_inline bool running(memprof_domain_t domain)
{
  memprof_thread_t thread = domain->current;

  if (thread && !thread->suspended) {
    return Running(domain_config(domain));
  }
  return false;
}

/* Renew the next sample in a domain's minor heap. Could race with
 * sampling and profile-stopping code, so do not call from another
 * domain unless the world is stopped. Must be called after each minor
 * sample and after each minor collection. In practice, this is called
 * at each minor sample, at each minor collection, and when sampling
 * is suspended and unsuspended. Extra calls do not change the
 * statistical properties of the sampling because of the
 * memorylessness of the geometric distribution. */

void caml_memprof_renew_minor_sample(caml_domain_state *state)
{
  memprof_domain_t domain = state->memprof;
  value *trigger = state->young_start;
  if (running(domain)) {
    /* set trigger based on geometric distribution */
  }
  CAMLassert((trigger >= state->young_start) &&
             (trigger <= state->young_ptr));
  state->memprof_young_trigger = trigger;
  caml_reset_young_limit(state);
}


void caml_memprof_track_alloc_shr(value block)
{
}

void caml_memprof_track_custom(value block, mlsize_t bytes)
{
}

void caml_memprof_track_young(uintnat wosize, int from_caml,
                              int nallocs, unsigned char* alloc_lens)
{
}

/**** Interface with systhread. ****/

CAMLexport memprof_thread_t caml_memprof_new_thread(caml_domain_state *state)
{
  return thread_create(state->memprof);
}

CAMLexport memprof_thread_t caml_memprof_main_thread(caml_domain_state *state)
{
  memprof_domain_t domain = state->memprof;
  memprof_thread_t thread = domain->threads;

  /* There should currently be just one thread in this domain */
  CAMLassert(thread);
  CAMLassert(thread->next == NULL);
  return thread;
}

CAMLexport void caml_memprof_delete_thread(memprof_thread_t thread)
{
  thread_destroy(thread);
}

CAMLexport void caml_memprof_enter_thread(memprof_thread_t thread)
{
  thread->domain->current = thread;
  update_suspended(thread->domain, thread->suspended);
}

/**** Interface to OCaml ****/

CAMLprim value caml_memprof_start(value lv, value szv, value tracker)
{
  CAMLparam3(lv, szv, tracker);
  CAMLlocal1(one_log1m_lambda_v);

  double lambda = Double_val(lv);
  intnat sz = Long_val(szv);

  /* Checks that [lambda] is within range (and not NaN). */
  if (sz < 0 || !(lambda >= 0.) || lambda > 1.)
    caml_invalid_argument("Gc.Memprof.start");

  memprof_domain_t domain = Caml_state->memprof;

  if (Running(domain_config(domain))) {
    caml_failwith("Gc.Memprof.start: already started.");
  }

  double one_log1m_lambda = lambda == 1.0 ? 0.0 : 1.0/caml_log1p(-lambda);
  one_log1m_lambda_v = caml_copy_double(one_log1m_lambda);

  value config = caml_alloc_shr(CONFIG_FIELDS, 0);
  caml_initialize(&Field(config, CONFIG_FIELD_STATUS),
                  Val_int(CONFIG_STATUS_RUNNING));
  caml_initialize(&Field(config, CONFIG_FIELD_LAMBDA), lv);
  caml_initialize(&Field(config, CONFIG_FIELD_1LOG1ML), one_log1m_lambda_v);
  caml_initialize(&Field(config, CONFIG_FIELD_FRAMES), szv);
  for (int i = CONFIG_FIELD_FIRST_CALLBACK;
       i <= CONFIG_FIELD_LAST_CALLBACK; ++i) {
    caml_initialize(&Field(config, i), Field(tracker,
                                             i - CONFIG_FIELD_FIRST_CALLBACK));
  }

  domain->config = config;

  caml_memprof_renew_minor_sample(Caml_state);

  CAMLreturn(config);
}

CAMLprim value caml_memprof_stop(value unit)
{
  memprof_domain_t domain = Caml_state->memprof;
  value config = domain_config(domain);

  if (config == CONFIG_NONE || Status(config) != CONFIG_STATUS_RUNNING) {
    caml_failwith("Gc.Memprof.stop: no profile running.");
  }
  Set_status(config, CONFIG_STATUS_STOPPED);

  caml_memprof_renew_minor_sample(Caml_state);

  return Val_unit;
}

CAMLprim value caml_memprof_discard(value config)
{
  uintnat status = Status(config);
  CAMLassert((status == CONFIG_STATUS_STOPPED) ||
             (status == CONFIG_STATUS_RUNNING) ||
             (status == CONFIG_STATUS_DISCARDED));

  switch (status) {
  case CONFIG_STATUS_STOPPED: /* correct case */
    break;
  case CONFIG_STATUS_RUNNING:
    caml_failwith("Gc.Memprof.discard: profile not stopped.");
  case CONFIG_STATUS_DISCARDED:
    caml_failwith("Gc.Memprof.discard: profile already discarded.");
  }

  Set_status(config, CONFIG_STATUS_DISCARDED);

  /* The config pointer from the domain state is cleared lazily (see
   * domain_config()). However, in the common case, we are discarding
   * the profile of the current domain, so let's clear that pointer
   * now. */
  (void)domain_config(Caml_state->memprof);

  return Val_unit;
}
