#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/mpcp.h>
#include <rtems/score/threadqimpl.h>

#define MPCP_TQ_OPERATIONS &_Thread_queue_Operations_priority
#define _ISR_lock_ISR_enable(_context) (void) _context;

/*@ ghost
  extern const int g_core;
  extern Scheduler_Control *g_homesched;
  extern Scheduler_Node *g_homenode;
  extern bool prioritiesUpdated;
  extern Thread_Control *g_thread_inherited;
  extern Thread_Control *g_thread_revoked;
  extern Thread_Control *g_new_owner;
  extern Priority_Control g_prio;
*/

/*@
  global invariant core_max: 0 <= g_core < 32;
  logic Thread_Control* MPCP_Owner(MPCP_Control *m) = m->Wait_queue.Queue.owner;
  logic Priority_Control MPCP_Ceiling(MPCP_Control *m) = m->Ceiling_priority.priority;
  logic Priority_Control MPCP_Localceiling(MPCP_Control *m) = m->ceiling_priorities[g_core];
  logic Priority_Control Executing_Priority = g_homenode->Wait.Priority.Node.priority;
  predicate MPCPThreadsWaiting(MPCP_Control *m) = m->Wait_queue.Queue.heads != NULL;
  predicate PriorityInherited(Thread_Control *t, Priority_Control p) = t == g_thread_inherited && p == g_prio && prioritiesUpdated;
  predicate PriorityRevoked(Thread_Control *t, Priority_Control p) = t == g_thread_revoked && p == g_prio && prioritiesUpdated;
*/

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _MPCP_Acquire_critical(
  MPCP_Control *mpcp,
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _MPCP_Release(
  MPCP_Control *mpcp,
  Thread_queue_Context *queue_context
);

/*@
  assigns \nothing;
  ensures \result == MPCP_Owner(mpcp);
*/
RTEMS_INLINE_ROUTINE Thread_Control *_MPCP_Get_owner(
  const MPCP_Control *mpcp
);

/*@
  requires \valid(mpcp);
  assigns mpcp->Wait_queue.Queue.owner;
  ensures MPCP_Owner(mpcp) == owner;
*/
RTEMS_INLINE_ROUTINE void _MPCP_Set_owner(
  MPCP_Control *mpcp,
  Thread_Control *owner
);

/*@
  requires \valid(mpcp) && \valid(scheduler);
  requires \valid(&mpcp->ceiling_priorities[0 .. g_core-1]);
  requires scheduler == g_homesched;
  assigns \nothing;
  ensures \result == MPCP_Localceiling(mpcp);
*/
RTEMS_INLINE_ROUTINE Priority_Control _MPCP_Get_priority(
  const MPCP_Control *mpcp,
  const Scheduler_Control *scheduler
);
/*@
  requires \valid(mpcp) && \valid(thread) && \valid(priority_node) && \valid(queue_context) && \valid(g_homesched) && \valid(g_homenode) && \valid(&g_homenode->Wait.Priority);
  requires \valid_read(&mpcp->ceiling_priorities[0 .. g_core-1]);
  behavior raise_success:
    assumes MPCP_Localceiling(mpcp) <= Executing_Priority;
    ensures Executing_Priority == MPCP_Localceiling(mpcp);
    ensures Executing_Priority == priority_node->priority;
    ensures priority_node->priority == MPCP_Localceiling(mpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures priority_node->priority == MPCP_Localceiling(mpcp);
    ensures g_thread_inherited == thread;
    ensures g_prio == MPCP_Localceiling(mpcp);
    ensures \result == STATUS_SUCCESSFUL;
    assigns g_homenode->Wait.Priority.Node.priority, g_thread_inherited, g_prio, priority_node->priority, queue_context->Priority.update_count;
  behavior raise_fail:
    assumes MPCP_Localceiling(mpcp) > Executing_Priority;
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    assigns queue_context->Priority.update_count;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MPCP_Raise_priority(
        MPCP_Control         *mpcp,
        Thread_Control       *thread,
        Priority_Node        *priority_node,
        Thread_queue_Context *queue_context
);

/*@
  requires \valid(thread) && \valid(priority_node) && \valid(queue_context) && \valid(g_homenode);
  assigns g_thread_revoked, g_prio, queue_context->Priority.update_count, g_homenode->Wait.Priority.Node.priority;
  ensures g_thread_revoked == thread && g_prio == priority_node->priority;
  ensures Executing_Priority >= \old(Executing_Priority);
*/
RTEMS_INLINE_ROUTINE void _MPCP_Remove_priority(
        Thread_Control       *thread,
        Priority_Node        *priority_node,
        Thread_queue_Context *queue_context
);

/*@
  requires \valid(mpcp) && \valid(thread) && \valid(ceiling_priority) && \valid(&mpcp->Ceiling_priority);
  ensures MPCP_Ceiling(mpcp) == Executing_Priority;
*/
RTEMS_INLINE_ROUTINE void _MPCP_Replace_priority(
        MPCP_Control   *mpcp,
        Thread_Control *thread,
        Priority_Node  *ceiling_priority
);

/*@
  requires \valid(mpcp) && \valid(executing) && \valid(queue_context) && \valid(g_homesched) && \valid(g_homenode) && \valid(&mpcp->Ceiling_priority);
  requires \valid_read(&mpcp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mpcp, executing, queue_context, g_homenode, g_homesched, &mpcp->Ceiling_priority);
  behavior claim_success:
    assumes MPCP_Localceiling(mpcp) <= Executing_Priority;
    ensures Executing_Priority == MPCP_Localceiling(mpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures MPCP_Owner(mpcp) == executing;
    ensures MPCP_Ceiling(mpcp) == MPCP_Localceiling(mpcp);
    ensures PriorityInherited(executing, MPCP_Ceiling(mpcp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior claim_fail:
    assumes MPCP_Localceiling(mpcp) > Executing_Priority;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MPCP_Claim_ownership(
        MPCP_Control         *mpcp,
        Thread_Control       *executing,
        Thread_queue_Context *queue_context
);

/*@
  requires \valid(mpcp) && \valid(executing) && \valid(queue_context) && \valid(g_homesched) && \valid(g_homenode) && \valid(&mpcp->Wait_queue.Queue) && \valid(MPCP_TQ_OPERATIONS);
  requires \valid_read(&mpcp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mpcp, executing, queue_context, g_homesched, g_homenode);
  behavior claim_success:
    assumes MPCP_Localceiling(mpcp) <= Executing_Priority;
    ensures Executing_Priority == MPCP_Localceiling(mpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures MPCP_Owner(mpcp) == executing;
    ensures MPCP_Ceiling(mpcp) == MPCP_Localceiling(mpcp);
    ensures PriorityInherited(executing, MPCP_Ceiling(mpcp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior claim_fail:
    assumes MPCP_Localceiling(mpcp) > Executing_Priority;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MPCP_Wait_for_ownership(
  MPCP_Control         *mpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(mpcp) && \valid(executing) && \valid(g_homesched) && \valid(g_homenode) && \valid(queue_context) && \valid(MPCP_TQ_OPERATIONS);
  requires \valid_read(&mpcp->ceiling_priorities[0 .. g_core-1]);
  requires executing != NULL;
  requires \separated(mpcp, executing, queue_context, g_homenode);
  behavior seize_free:
    assumes MPCP_Owner(mpcp) == NULL && Executing_Priority >= MPCP_Localceiling(mpcp);
    ensures MPCP_Owner(mpcp) == executing;
    ensures Executing_Priority == MPCP_Localceiling(mpcp)
      && Executing_Priority <= \old(Executing_Priority);
    ensures MPCP_Ceiling(mpcp) == MPCP_Localceiling(mpcp);
    ensures PriorityInherited(executing, MPCP_Ceiling(mpcp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior seize_wait:
    assumes MPCP_Owner(mpcp) != NULL
      && MPCP_Owner(mpcp) != executing
      && Executing_Priority >= MPCP_Localceiling(mpcp)
      && wait;
    ensures MPCP_Owner(mpcp) == executing;
    ensures Executing_Priority == MPCP_Localceiling(mpcp)
      && Executing_Priority <= \old(Executing_Priority);
    ensures MPCP_Ceiling(mpcp) == MPCP_Localceiling(mpcp);
    ensures PriorityInherited(executing, MPCP_Ceiling(mpcp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior seize_no_wait_not_free:
    assumes MPCP_Owner(mpcp) != NULL
      && MPCP_Owner(mpcp) != executing
      && Executing_Priority >= MPCP_Localceiling(mpcp)
      && !wait;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    ensures \result == STATUS_UNAVAILABLE;
  behavior seize_fail_selfowned:
    assumes MPCP_Owner(mpcp) == executing;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    ensures \result == STATUS_UNAVAILABLE;
  behavior seize_fail_ceiling:
    assumes Executing_Priority < MPCP_Localceiling(mpcp)
      && MPCP_Owner(mpcp) != executing;
    ensures MPCP_Owner(mpcp) == \old(MPCP_Owner(mpcp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED || STATUS_UNAVAILABLE;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MPCP_Seize(
        MPCP_Control         *mpcp,
        Thread_Control       *executing,
        bool                  wait,
        Thread_queue_Context *queue_context
);

/*@
  requires \valid(mpcp) && \valid(&mpcp->Wait_queue.Queue) && \valid(&mpcp->Wait_queue.Queue.heads) && \valid(executing) && \valid(queue_context) && \valid(g_homenode) && \valid(MPCP_TQ_OPERATIONS);
  requires \separated(mpcp, executing, queue_context, g_homenode);
  behavior surrender_no_successor:
    assumes MPCP_Owner(mpcp) == executing;
    assumes !MPCPThreadsWaiting(mpcp);
    ensures MPCP_Owner(mpcp) == NULL;
    ensures PriorityRevoked(executing, MPCP_Ceiling(mpcp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures \result == STATUS_SUCCESSFUL;
  behavior surrender_successor:
    assumes MPCP_Owner(mpcp) == executing;
    assumes MPCPThreadsWaiting(mpcp);
    ensures PriorityRevoked(executing, MPCP_Ceiling(mpcp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures MPCP_Owner(mpcp) == executing;
    ensures \result == STATUS_SUCCESSFUL;
  behavior surrender_fail:
    assumes MPCP_Owner(mpcp) != executing;
    ensures \result == STATUS_NOT_OWNER;
  disjoint behaviors;
  complete behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MPCP_Surrender(
        MPCP_Control         *mpcp,
        Thread_Control       *executing,
        Thread_queue_Context *queue_context
);

/*@
  requires \valid(the_thread);
  assigns \nothing;
  ensures \result == g_homesched;
*/
RTEMS_INLINE_ROUTINE const Scheduler_Control *_Thread_Scheduler_get_home(
  const Thread_Control *the_thread
);

/*@
  requires \valid(the_thread);
  assigns \nothing;
  ensures \result == g_homenode;
*/
RTEMS_INLINE_ROUTINE Scheduler_Node *_Thread_Scheduler_get_home_node(
  const Thread_Control *the_thread
);

/*@
  requires \valid(node);
  ensures node->priority == priority;
  assigns node->priority;
*/
RTEMS_INLINE_ROUTINE void _Priority_Node_initialize(
  Priority_Node *node,
  Priority_Control priority
);

/*@
  requires \valid(the_thread) && \valid(priority_node) && \valid(queue_context);
  assigns g_thread_inherited, g_prio, g_homenode->Wait.Priority.Node.priority;
  ensures g_thread_inherited == the_thread && g_prio == priority_node->priority;
  ensures Executing_Priority <= \old(Executing_Priority);
  ensures Executing_Priority == priority_node->priority;
  ensures the_thread->Scheduler.nodes->Wait.Priority.Node.priority == priority_node->priority;
  ensures priority_node->priority == \old(priority_node->priority);
*/
void _Thread_Priority_add(
  Thread_Control *the_thread,
  Priority_Node *priority_node,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(the_thread) && \valid(priority_node) && \valid(queue_context) && \valid(g_homenode);
  assigns g_homenode->Wait.Priority.Node.priority, g_thread_revoked, g_prio;
  ensures g_thread_revoked == the_thread && g_prio == priority_node->priority;
  ensures Executing_Priority == priority_node->priority;
  ensures Executing_Priority > \old(Executing_Priority);
*/
void _Thread_Priority_remove(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(queue) && \valid(the_thread) && \valid(operations) && \valid(queue_context);
  assigns queue->owner, prioritiesUpdated;
  ensures queue->owner == the_thread;
  ensures the_thread == \old(the_thread);
  ensures prioritiesUpdated;
*/
void _Thread_queue_Enqueue(
  Thread_queue_Queue *queue,
  const Thread_queue_Operations *operations,
  Thread_Control *the_thread,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(queue) && \valid(heads) && \valid(previous_owner) && \valid(queue_context) && \valid(operations);
  requires queue->owner == NULL;
  assigns queue->owner, prioritiesUpdated;
  ensures queue->owner == g_new_owner;
  ensures prioritiesUpdated;
*/
void _Thread_queue_Surrender(
  Thread_queue_Queue            *queue,
  Thread_queue_Heads            *heads,
  Thread_Control                *previous_owner,
  Thread_queue_Context          *queue_context,
  const Thread_queue_Operations *operations
);

/*@
  assigns prioritiesUpdated;
  ensures prioritiesUpdated;
*/
void _Thread_Priority_update(
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(aggregation);
  ensures \result == aggregation->Node.priority;
  ensures \result == Executing_Priority;
  assigns \nothing;
*/
RTEMS_INLINE_ROUTINE Priority_Control _Priority_Get_priority(
  const Priority_Aggregation *aggregation
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_set_deadlock_callout(
  Thread_queue_Context          *queue_context,
  Thread_queue_Deadlock_callout  deadlock_callout
);

/*@
  requires \valid(queue_context);
  assigns queue_context->Priority.update_count;
  ensures queue_context->Priority.update_count == 0;
*/
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_clear_priority_updates(
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_acquire_default_critical(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_release_default_critical(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_acquire_default(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_release_default(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_queue_Dispatch_disable(
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_Dispatch_disable_critical(
  const ISR_lock_Context *lock_context
);

//@ assigns \nothing;
void _Thread_Dispatch_enable( Per_CPU_Control *cpu_self );

/*@
  requires \valid(queue_context);
  assigns queue_context->thread_state;
  ensures queue_context->thread_state == thread_state;
*/
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_set_thread_state(
  Thread_queue_Context *queue_context,
  States_Control        thread_state
);

/*@
  requires \valid(the_thread);
  requires \valid(victim_node);
  requires \valid(replacement_node);
  ensures Executing_Priority == replacement_node->priority;
  assigns g_homenode->Wait.Priority.Node.priority;
*/
void _Thread_Priority_replace(
  Thread_Control *the_thread,
  Priority_Node  *victim_node,
  Priority_Node  *replacement_node
);