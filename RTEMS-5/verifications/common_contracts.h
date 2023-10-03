/************************************************/

//				 GHOST VARIABLE(S)

/************************************************/
/*@ ghost
   extern Scheduler_Node *g_homenode;
 */
/************************************************/

//	 LOWER LAYER FUNCTIONS COMMONLY ANNOTATED

/************************************************/
/*@
  
  assigns \nothing;
  ensures \result == g_homenode;
*/
//requires \valid(the_thread);
RTEMS_INLINE_ROUTINE Scheduler_Node *_Thread_Scheduler_get_home_node(
  const Thread_Control *the_thread
);
/*@
   
   assigns \nothing;
   ensures \result == the_thread->Scheduler.home_scheduler;
 */
 //requires \valid(the_thread);
RTEMS_INLINE_ROUTINE const Scheduler_Control *_Thread_Scheduler_get_home(
  const Thread_Control *the_thread
);
/*@
   assigns queue_context->thread_state;
   ensures queue_context->thread_state == thread_state;
 */ // no fmlps
RTEMS_INLINE_ROUTINE void
_Thread_queue_Context_set_thread_state(
  Thread_queue_Context *queue_context,
  States_Control        thread_state
);
/*@
   assigns queue_context->deadlock_callout;
   ensures queue_context->deadlock_callout == deadlock_callout;
 */
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_set_deadlock_callout(
  Thread_queue_Context          *queue_context,
  Thread_queue_Deadlock_callout  deadlock_callout
);
/*@
    assigns \nothing;
    ensures \result == aggregation->Node.priority;
 */
RTEMS_INLINE_ROUTINE Priority_Control _Priority_Get_priority(
  const Priority_Aggregation *aggregation
);
/************************************************/

//	 LOWER LAYER FUNCTIONS COMMONLY ABSTRACTED

/************************************************/
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Acquire_critical(
  Thread_queue_Control *the_thread_queue,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
void _Thread_Dispatch_enable( Per_CPU_Control *cpu_self );
//@ assigns \nothing; //surrender
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
void _Thread_queue_Release(
  Thread_queue_Control *the_thread_queue,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_Dispatch_disable_critical(
  const ISR_lock_Context *lock_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Priority_Node_initialize(
  Priority_Node    *node,
  Priority_Control  priority
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_queue_Dispatch_disable(
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
void _Thread_queue_Enqueue(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Destroy(
  Thread_queue_Control *the_thread_queue
);
