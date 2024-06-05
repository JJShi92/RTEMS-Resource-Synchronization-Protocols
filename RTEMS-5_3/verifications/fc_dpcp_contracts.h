#include <rtems/score/dpcp.h>
#include <rtems/score/threadqimpl.h>


#define STATES_WAITING_FOR_MUTEX 0x00000001
#define CORE_MUTEX_TQ_OPERATIONS &_Thread_queue_Operations_priority
#define DPCP_TQ_OPERATIONS &_Thread_queue_Operations_priority

/*@ ghost
  extern Scheduler_Node *g_homenode;
  extern bool prioritiesUpdated;
  extern Thread_Control *g_thread_inherited;
  extern Thread_Control *g_thread_revoked;
  extern Thread_Control *g_new_owner;
  extern Priority_Control g_prio;
*/

/*@
  logic Thread_Control* DPCP_Owner(DPCP_Control *m) = m->Wait_queue.Queue.owner;
  logic Priority_Control DPCP_Ceiling(DPCP_Control *m) = m->Ceiling_priority.priority;
  logic Priority_Control Executing_Priority = g_homenode->Wait.Priority.Node.priority;
  predicate DPCPThreadsWaiting(DPCP_Control *m) = m->Wait_queue.Queue.heads != NULL;
  predicate PriorityInherited(Thread_Control *t, Priority_Control p) = t == g_thread_inherited && p == g_prio && prioritiesUpdated;
  predicate PriorityRevoked(Thread_Control *t, Priority_Control p) = t == g_thread_revoked && p == g_prio && prioritiesUpdated;
  logic Per_CPU_Control* DPCP_CPU(Thread_Control *executing) = executing->Scheduler.cpu;
*/

/*@
  requires \valid(executing) && \valid(dpcp->cpu) && \valid(&dpcp->Ceiling_priority) && \valid(g_homenode);
  requires \separated(executing, dpcp);
  assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  ensures DPCP_CPU(executing) == dpcp->cpu;
  ensures Executing_Priority == DPCP_Ceiling(dpcp);
  ensures prioritiesUpdated;
  ensures g_thread_inherited == executing && g_prio == DPCP_Ceiling(dpcp);
  ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
*/
RTEMS_INLINE_ROUTINE void _DPCP_Migrate(
  Thread_Control *executing,
  DPCP_Control   *dpcp
);

/*@
  requires \valid(executing) && \valid(migration_cpu) && \valid(ceiling_priority) && \valid(g_homenode);
  assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  ensures DPCP_CPU(executing) == migration_cpu;
  ensures Executing_Priority == ceiling_priority->priority;
  ensures g_thread_inherited == executing && g_prio == ceiling_priority->priority;
  ensures prioritiesUpdated;
*/
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_To(
  Thread_Control  *executing,
  Per_CPU_Control *migration_cpu,
  Priority_Node   *ceiling_priority
);

/*@
  requires \valid(executing) && \valid(dpcp->cpu) && \valid(g_homenode);
  requires \separated(executing, dpcp);
  assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  ensures DPCP_CPU(executing) == DPCP_CPU(g_thread_revoked);
  ensures g_thread_revoked == executing;
  ensures g_prio == executing->Real_priority.priority;
*/
RTEMS_INLINE_ROUTINE void _DPCP_Migrate_Back(
  Thread_Control *executing,
  DPCP_Control   *dpcp
);

/*@
  requires \valid(executing) && \valid(migration_cpu) && \valid(g_homenode);
  assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  ensures DPCP_CPU(executing) == DPCP_CPU(g_thread_revoked);
  ensures Executing_Priority == executing->Real_priority.priority;
  ensures g_thread_revoked == executing && g_prio == Executing_Priority;
  ensures prioritiesUpdated;
*/
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_Back(
  Thread_Control  *executing,
  Per_CPU_Control *migration_cpu
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Acquire_critical(
  DPCP_Control         *dpcp,
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Release(
  DPCP_Control         *dpcp,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp);
  assigns \result \from dpcp;
  ensures \result == DPCP_Owner(dpcp) == dpcp->Wait_queue.Queue.owner;
*/
RTEMS_INLINE_ROUTINE Thread_Control *_DPCP_Get_owner(
  const DPCP_Control *dpcp
);

/*@
  requires \valid(dpcp);
  assigns dpcp->Wait_queue.Queue.owner \from owner;
  ensures DPCP_Owner(dpcp) == owner;
*/
RTEMS_INLINE_ROUTINE void _DPCP_Set_owner(
  DPCP_Control   *dpcp,
  Thread_Control *owner
);

/*@
  requires \valid(dpcp);
  assigns \nothing;
  ensures \result == DPCP_Ceiling(dpcp);
*/
RTEMS_INLINE_ROUTINE Priority_Control _DPCP_Get_Priority(
  const DPCP_Control      *dpcp
);

/*@
  requires \valid(dpcp);
  requires \valid(queue_context);
  assigns dpcp->Ceiling_priority.priority;
*/
RTEMS_INLINE_ROUTINE void _DPCP_Set_priority(
  DPCP_Control         *dpcp,
  Priority_Control      priority_ceiling,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp) && \valid(executing) && \valid(queue_context) && \valid(g_homenode) &&  \valid(dpcp->cpu);
  requires \separated(dpcp, executing, queue_context, g_homenode);
  behavior raise_success:
    assumes Executing_Priority >= DPCP_Ceiling(dpcp);
    ensures DPCP_Owner(dpcp) == executing;
    ensures DPCP_CPU(executing) == dpcp->cpu;
    ensures Executing_Priority == DPCP_Ceiling(dpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures PriorityInherited(executing, DPCP_Ceiling(dpcp));
    ensures \result == STATUS_SUCCESSFUL;
    assigns dpcp->Wait_queue.Queue.owner, g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior raise_fail:
    assumes Executing_Priority < DPCP_Ceiling(dpcp);
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    assigns \nothing;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Claim_ownership(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp) && \valid(executing) && \valid(queue_context) && \valid(g_homenode) && \valid(DPCP_TQ_OPERATIONS);
  requires \separated(dpcp, executing, queue_context, g_homenode);
  behavior raise_success:
    assumes Executing_Priority >= DPCP_Ceiling(dpcp);
    ensures DPCP_Owner(dpcp) == executing;
    ensures DPCP_CPU(executing) == dpcp->cpu;
    ensures Executing_Priority == DPCP_Ceiling(dpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures PriorityInherited(executing, DPCP_Ceiling(dpcp));
    ensures \result == STATUS_SUCCESSFUL;
    assigns dpcp->Wait_queue.Queue.owner, g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior raise_fail:
    assumes Executing_Priority < DPCP_Ceiling(dpcp);
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    assigns \nothing;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Wait_for_ownership(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp) && \valid(executing) && \valid(g_homenode) && \valid(queue_context) && \valid(dpcp->Wait_queue.Queue.owner) && \valid(DPCP_TQ_OPERATIONS);
  requires \separated(dpcp, executing, queue_context, g_homenode);
  requires executing != NULL;
  behavior seize_free:
    assumes DPCP_Owner(dpcp) == NULL && Executing_Priority >= DPCP_Ceiling(dpcp);
    ensures DPCP_Owner(dpcp) == executing;
    ensures DPCP_CPU(executing) == dpcp->cpu;
    ensures Executing_Priority == DPCP_Ceiling(dpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures PriorityInherited(executing, DPCP_Ceiling(dpcp));
    ensures \result == STATUS_SUCCESSFUL;
    assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior seize_wait:
    assumes DPCP_Owner(dpcp) != NULL
      && DPCP_Owner(dpcp) != executing
      && Executing_Priority >= DPCP_Ceiling(dpcp)
      && wait;
    ensures DPCP_Owner(dpcp) == executing;
    ensures DPCP_CPU(executing) == dpcp->cpu;
    ensures Executing_Priority == DPCP_Ceiling(dpcp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures PriorityInherited(executing, DPCP_Ceiling(dpcp));
    ensures \result == STATUS_SUCCESSFUL;
    assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior seize_no_wait_not_free:
    assumes DPCP_Owner(dpcp) != NULL
      && DPCP_Owner(dpcp) != executing
      && Executing_Priority >= DPCP_Ceiling(dpcp)
      && !wait;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    ensures \result == STATUS_UNAVAILABLE;
    assigns \nothing;
  behavior seize_fail_selfowned:
    assumes DPCP_Owner(dpcp) == executing;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    ensures \result == STATUS_UNAVAILABLE;
    assigns \nothing;
  behavior seize_fail_ceiling:
    assumes Executing_Priority < DPCP_Ceiling(dpcp)
      && DPCP_Owner(dpcp) != executing;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED || STATUS_UNAVAILABLE;
    assigns \nothing;
  complete behaviors;
  disjoint behaviors;
*/  
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Seize(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp) && \valid(&dpcp->Wait_queue.Queue) && \valid(&dpcp->Wait_queue) && \valid(executing) && \valid(queue_context) && \valid(g_homenode) && \valid(DPCP_TQ_OPERATIONS);
  requires \separated(dpcp, executing, queue_context, g_homenode);
  behavior surrender_no_successor:
    assumes DPCP_Owner(dpcp) == executing;
    assumes !DPCPThreadsWaiting(dpcp);
    ensures DPCP_Owner(dpcp) == NULL;
    ensures PriorityRevoked(executing, DPCP_Ceiling(dpcp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures DPCP_CPU(executing) == DPCP_CPU(g_thread_inherited);
    ensures \result == STATUS_SUCCESSFUL;
    assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior surrender_successor:
    assumes DPCP_Owner(dpcp) == executing;
    assumes DPCPThreadsWaiting(dpcp);
    ensures PriorityRevoked(executing, DPCP_Ceiling(dpcp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures DPCP_Owner(dpcp) == executing;
    ensures DPCP_CPU(executing) == dpcp->cpu;
    ensures \result == STATUS_SUCCESSFUL;
    assigns g_homenode->Wait.Priority.Node.priority, g_prio, prioritiesUpdated;
  behavior surrender_fail:
    assumes DPCP_Owner(dpcp) != executing;
    ensures DPCP_Owner(dpcp) == \old(DPCP_Owner(dpcp));
    ensures \result == STATUS_NOT_OWNER;
    assigns \nothing;
  disjoint behaviors;
  complete behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Surrender(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(dpcp);
  assigns \nothing;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Can_destroy(
  DPCP_Control *dpcp
);

/*@
  requires \valid(aggregation);
  assigns \result \from aggregation;
  ensures \result == aggregation->Node.priority == Executing_Priority;
*/
RTEMS_INLINE_ROUTINE Priority_Control _Priority_Get_priority(
  const Priority_Aggregation *aggregation
);

/*@
  requires \valid(the_thread);
  assigns \result \from the_thread;
  ensures \result == g_homenode;
*/
RTEMS_INLINE_ROUTINE Scheduler_Node *_Thread_Scheduler_get_home_node(
  const Thread_Control *the_thread
);

/*@
  requires \valid(queue) && \valid(the_thread) && \valid(operations) && \valid(queue_context);
  assigns queue->owner \from the_thread;
  assigns prioritiesUpdated;
  ensures queue->owner == the_thread;
  ensures prioritiesUpdated;
*/
void _Thread_queue_Enqueue(
  Thread_queue_Queue *queue,
  const Thread_queue_Operations *operations,
  Thread_Control *the_thread,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(queue_context);
  assigns queue_context->deadlock_callout;
  ensures queue_context->deadlock_callout == deadlock_callout;
*/
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

//@ assigns \result \from queue_context;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_queue_Dispatch_disable(
  Thread_queue_Context *queue_context
);

/*@ 
  assigns \result \from lock_context;
  ensures \result == DPCP_CPU(g_thread_inherited);
*/
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

//@ assigns \nothing;
void _Thread_queue_Extract_critical(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);

/*@
  requires \valid(the_thread_queue) && \valid(operations);
  assigns \result \from the_thread_queue;
  behavior successor:
    assumes the_thread_queue->Queue.heads != NULL;
    ensures \result == g_new_owner;
  behavior no_successor:
    assumes the_thread_queue->Queue.heads == NULL;
    ensures \result == NULL;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Thread_Control *_Thread_queue_First_locked(
  Thread_queue_Control          *the_thread_queue,
  const Thread_queue_Operations *operations
);


//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Acquire_critical(
  Thread_queue_Control *the_thread_queue,
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
void _Thread_queue_Release(
  Thread_queue_Control *the_thread_queue,
  Thread_queue_Context *queue_context
);