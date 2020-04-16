#define CONFIGURE_INIT
#define CONFIGURE_MAXIMUM_USER_EXTENSIONS 1
#include "system.h"
#include "stdio.h"
#include <assert.h>

rtems_id sid;
rtems_id tasks[7];

rtems_status_code rsc; //tmp variable for status code
rtems_id scheds[3]; //scheduler ids
rtems_id schid;

rtems_task task_entry( rtems_task_argument argument );
rtems_task task_entry2( rtems_task_argument argument );

void print_name( rtems_id id );
void init_sched();

void init_sched(
)
{
  uint32_t cpu_index;
  printf( "PROCESSOR COUNT: %d\n",rtems_get_processor_count() );
  for ( cpu_index = 0; cpu_index < 3; cpu_index++ ) {
    rsc = rtems_scheduler_ident_by_processor( cpu_index, &scheds[cpu_index] );
    printf( "rtems_scheduler_by_processor(%d, &scheds[%d]): %s\n", cpu_index,cpu_index, rtems_status_text( rsc ) );
    printf( "%d\n",scheds[cpu_index] );
  }
}

rtems_task init(
rtems_task_argument argument
)
{
  printf( "TEST START:\n" );
  init_sched();
  
  /* Normal Task: */
  int i;
  int j = 5;
  for ( i = 0; i < 7; i++) {
    rsc = rtems_task_create(
      rtems_build_name( 'T', 'A', 'S', '0'+ i ),
      i+2,
      RTEMS_MINIMUM_STACK_SIZE, RTEMS_PREEMPT,
      RTEMS_NO_FLOATING_POINT, &tasks[i]
    );
    printf( "Create task %d: %s\n", i, rtems_status_text( rsc ) );
  }

  rsc = rtems_semaphore_create(
    rtems_build_name( 'H', 'D', 'G', 'A' ),
    1, 
    ( RTEMS_BINARY_SEMAPHORE | RTEMS_HYPERPERIOD_DEPENDENCY_GRAPH_APPROACH| RTEMS_GLOBAL ),
    7, 
    &sid
  );
  printf( "Create HDGA Semaphore: %s\n", rtems_status_text( rsc ) );

  /* CPU#0 */
  rtems_task_set_scheduler( tasks[0], scheds[0], 7 );
  rtems_task_set_scheduler( tasks[1], scheds[0], 6 );
  rtems_task_set_scheduler( tasks[6], scheds[0], 6 );
  
   /* CPU#1 */
  rtems_task_set_scheduler( tasks[2], scheds[1], 5 );
  rtems_task_set_scheduler( tasks[3], scheds[1], 4 );
  
   /* CPU#2 */
  rtems_task_set_scheduler( tasks[4], scheds[2], 2 );
  rtems_task_set_scheduler( tasks[5], scheds[2], 4 );

  rsc = rtems_semaphore_ticket( sid, tasks[0], 5 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 0, 5, rtems_status_text( rsc ) );
   
  rsc = rtems_semaphore_ticket( sid, tasks[1], 4 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 1, 4, rtems_status_text( rsc ) );
   
  rsc = rtems_semaphore_ticket( sid, tasks[2], 0 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 2, 0, rtems_status_text( rsc ) );
  
  rsc = rtems_semaphore_ticket( sid, tasks[3], 3 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 3, 3, rtems_status_text( rsc ) );
   
  rsc = rtems_semaphore_ticket( sid, tasks[4], 2 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 4, 2, rtems_status_text( rsc ) );
   
  rsc = rtems_semaphore_ticket( sid, tasks[5], 1 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 5, 1, rtems_status_text( rsc ) );
  
  rsc = rtems_semaphore_ticket( sid, tasks[6], 6 );
  printf( "setting ticket for semaphore sid for thread %d, ticket %d: %s\n", 6, 6, rtems_status_text( rsc ) );
    
  //=> 2,5,4,3,1,0,6

  printf( "HDGA\n" );
  for ( i = 0; i < 6; i++ ) {
    if ( i != 1 ) {
      rtems_task_start( tasks[i], task_entry, i );
      rtems_task_wake_after( 100 );
    }
  }
  rtems_task_start( tasks[1], task_entry2, 1 );
  
  rsc = rtems_task_delete( RTEMS_SELF );    /* should not return */
}

/* Delaying the start of thread 6 to see if the order is still correct. */
rtems_task task_entry(
rtems_task_argument i
)
{
  rtems_name name;
  rtems_status_code status;

  status = rtems_semaphore_obtain( sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT );
  
  for ( int j = 0; j < 10000000; j++ ) {
    asm volatile ( "nop" );
  }
  printf( "->Thread %d Releasing semaphore...\n", i);
  status = rtems_semaphore_release( sid );
 
  if ( i == 0 ) {
    rtems_task_start(tasks[6], task_entry, 6);
  }
  
  status = rtems_task_delete( RTEMS_SELF );    /* should not return */
  printf( "rtems_task_delete returned with status of %d.\n", status );
}

/*Delaying thread 1 to see if the order is still correct */
rtems_task task_entry2(
rtems_task_argument i
)
{
  rtems_name name;
  rtems_status_code status;

  status = rtems_semaphore_obtain( sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT );
  
  for ( int j = 0; j < 10000000; j++) {
    asm volatile ( "nop" );
  }
  printf( "->Thread %d Releasing semaphore...\n", i );
  status = rtems_semaphore_release( sid );
 
  status = rtems_semaphore_obtain(sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  
  for(int j = 0; j < 10000000; j++) {
    asm volatile ( "nop" );
  }
  printf( "->Thread %d Releasing semaphore...\n" , i, i);
  status = rtems_semaphore_release(sid);
  
  if ( i == 0 ) {
    rtems_task_start( tasks[6], task_entry, 6 );
  }
  status = rtems_task_delete( RTEMS_SELF );    /* should not return */
  printf( "rtems_task_delete returned with status of %d.\n", status );
}

void print_name(
rtems_id id
)
{
  char  buffer[10];   /* name assumed to be 10 characters or less */
  char *result;
  result = rtems_object_get_name( id, sizeof( buffer ), buffer );
  printk( "ID=0x%08x name=%s\n", id, ( ( result ) ? result : "no name" ) );
}

