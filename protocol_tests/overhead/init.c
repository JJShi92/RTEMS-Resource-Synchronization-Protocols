/*
 *
*/

#define CONFIGURE_INIT
#include "system.h"
#include "stdio.h"
#include <assert.h>

int counter = 0;
rtems_id sid[3];
rtems_id tasks[15];
rtems_id periods[15];
int priorities[15] = {10,10,10,9,9,9,8,8,8,7,7,7,6,6,6};

rtems_status_code rsc; //tmp variable for status code
rtems_id scheds[4]; //scheduler ids

void print_name( rtems_id id );
void init_sched();
void create_and_set_task( int i, rtems_task_entry entry_point, rtems_id scheduler_id, int priority );
int get_priority_self();
int get_priority_by_id( rtems_id id );

rtems_task task_entry( rtems_task_argument i );
rtems_task task_entry1( rtems_task_argument i );
rtems_task task_entry2( rtems_task_argument i );
rtems_task_entry entry_points[3] = {task_entry, task_entry1, task_entry2};


void create_and_set_task( 
  int              i, 
  rtems_task_entry entry_point, 
  rtems_id         scheduler_id,
  int              priority
) 
{
  rsc = rtems_task_create(
    rtems_build_name ('T', 'A', 'S', '0' + i), 
    1+i, 
    RTEMS_MINIMUM_STACK_SIZE, RTEMS_PREEMPT, 
    RTEMS_NO_FLOATING_POINT,
    &tasks[i]
  );
  
  //printf( "create task %d: %s\n", i, rtems_status_text( rsc ) );
  rtems_task_set_scheduler( 
    tasks[i],
    scheduler_id,
    priority
  );
  
  rtems_task_start( tasks[i], entry_point, i );
  rtems_task_wake_after( 100 );
}

int get_priority_self(
)
{
  return get_priority_by_id( RTEMS_SELF );
}

int get_priority_by_id(
  rtems_id id
)
{
  rtems_task_priority rtp;
  rtems_id sched;
  rtems_task_get_scheduler( id, &sched );
  rtems_task_get_priority( id, sched, &rtp);
  return ( int ) rtp;
}

void init_sched(
) 
{
  uint32_t cpu_index;
  printf( "PROCESSOR COUNT: %d\n", rtems_get_processor_count() );
  for ( cpu_index = 0; cpu_index < 4; cpu_index++ ) {
    rsc = rtems_scheduler_ident_by_processor( cpu_index, &scheds[cpu_index] );
    printf( "rtems_scheduler_by_processor( %d, &scheds[%d] ): %s\n", 
      cpu_index,cpu_index, 
      rtems_status_text( rsc )
    );
    printf( "%d\n", scheds[cpu_index] );
  }
}

rtems_task init 
(
  rtems_task_argument argument
)
{
  printf( "TEST START:\n" );
  init_sched();
  /* Creating semaphores */
  for ( int i = 0; i < 3; i++ ) {
    /*
    rsc = rtems_semaphore_create(
      rtems_build_name( 'D', 'P', 'C', '0' + i ), 
      1,
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL ), 
      1, 
      &sid[i]
    );
    printf( "Create DPCP Semaphore: %s\n", rtems_status_text( rsc ) );
    */
    
    /*
    rsc = rtems_semaphore_create(
      rtems_build_name( 'D', 'F', 'L', '0' + i ), 
      1, 
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_FLEXIBLE_LOCKING_LONG |RTEMS_GLOBAL),
      1, 
      &sid[i]
    );    
    printf ( "Create DFLPL Semaphore: %s\n", rtems_status_text( rsc ) );
    */
    
    /*
    rsc = rtems_semaphore_create(
      rtems_build_name( 'M', 'R', 'S', '0' + i ), 
      1,
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_MULTIPROCESSOR_RESOURCE_SHARING ), 
      1, 
      &sid[i]
    );
    printf( "Create MRSP Semaphore: %s\n", rtems_status_text( rsc ) );
    */
    
    /*
    rsc = rtems_semaphore_create(
      rtems_build_name ( 'M', 'P', 'C', '0' + i ), 1,
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_MULTIPROCESSOR_PRIORITY_CEILING ), 
      1, 
      &sid[i]
    );
    printf( "Create MPCP Semaphore: %s\n", rtems_status_text( rsc ) );
    */
    
    rsc = rtems_semaphore_create(
      rtems_build_name ( 'F', 'M', 'P', '0' + i ),
      1,
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_FLEXIBLE_MULTIPROCESSOR_LOCKING_LONG | RTEMS_FIFO | RTEMS_GLOBAL ), 
      1, 
      &sid[i]
    );
    printf( "Create FLPL Semaphore: %s\n", rtems_status_text( rsc ) );
    
    /*
    rsc = rtems_semaphore_create(
      rtems_build_name ( 'F', 'L', 'P', '0' + i ), 
      1,
      ( RTEMS_BINARY_SEMAPHORE | RTEMS_FLEXIBLE_MULTIPROCESSOR_LOCKING_SHORT | RTEMS_FIFO | RTEMS_GLOBAL ), 
      1, 
      &sid[i]
    );
    printf( "Create FLPS Semaphore: %s\n", rtems_status_text( rsc ) );
    */
  }
    
  /*Tier 1 tasks */  
  create_and_set_task( 0, task_entry, scheds[0], priorities[0] );
  create_and_set_task( 1, task_entry1, scheds[2], priorities[1] );
  create_and_set_task( 2, task_entry2, scheds[3], priorities[2] );

  /*Tier 2 tasks */   
  create_and_set_task( 3, task_entry1, scheds[0], priorities[3] );
  create_and_set_task( 4, task_entry2, scheds[2], priorities[4] );
  create_and_set_task( 5, task_entry, scheds[3], priorities[5] );

  /*Tier 3 tasks */  
  create_and_set_task( 6, task_entry2, scheds[0], priorities[6] );
  create_and_set_task( 7, task_entry, scheds[2], priorities[7] );
  create_and_set_task( 8, task_entry1, scheds[3], priorities[8] );

  /*Tier 4 tasks */
  create_and_set_task( 9, task_entry1, scheds[0], priorities[9]);
  create_and_set_task( 10, task_entry2, scheds[2], priorities[10]);
  create_and_set_task( 11, task_entry, scheds[3], priorities[11]);

  /*Tier 5 tasks */ 
  create_and_set_task( 12, task_entry2, scheds[0], priorities[12] );
  create_and_set_task( 13, task_entry, scheds[2], priorities[13] );
  create_and_set_task( 14, task_entry1, scheds[3], priorities[14] );

  rsc = rtems_task_delete( RTEMS_SELF ); 
}

rtems_task task_entry(
  rtems_task_argument i
)
{
  //printf( "Task %d started\n", i );
  rtems_name name;
  rtems_status_code status;
  name = rtems_build_name( 'P', 'E', 'R', '0' + i );
  status = rtems_rate_monotonic_create( name, &periods[i] );
  //printf( "create monotonic: %d: %s\n", i, rtems_status_text( status ) );
  int period;
  period = priorities[i];
  period = period * 15;
        
  while ( 1 ) {
    if (rtems_rate_monotonic_period( periods[i], period ) == RTEMS_TIMEOUT) {
      printf( "missed period. task %d.\n", i );
      break;
    }
    status = rtems_semaphore_obtain( sid[0], RTEMS_WAIT, RTEMS_NO_TIMEOUT );
    //printf( "L;%d\n", status );
        
    for ( int j = 0; j < 1000000; j++ ) {
      asm volatile( "nop" );
    }
    status = rtems_semaphore_release( sid[0] );
    //printf( "U;%d\n", status );
    //printf( "Task %d:N P:%d\n", i, get_priority_self( ) );
  }
  status = rtems_rate_monotonic_delete( periods[i] );
        
  if ( status != RTEMS_SUCCESSFUL ) {
    printf( "rtems_rate_monotonic_delete failed with status of %d.\n", status );
  }
  status = rtems_task_delete( RTEMS_SELF );    /* should not return */
  printf( "rtems_task_delete returned with status of %d.\n", status );
}

rtems_task task_entry1( 
  rtems_task_argument i 
)
{
  //printf( "Task %d started\n", i );
  rtems_name name;
  rtems_status_code status;
  rtems_status_code unlock = 0;
  rtems_status_code lock = 0;
  name = rtems_build_name ('P', 'E', 'R', '0' + i);
  status = rtems_rate_monotonic_create ( name, &periods[i] );
  //printf( "create monotonic: %d: %s\n", i, rtems_status_text( status ) );
  int period;
  period = priorities[i];
  period = period * 15;
        
  while ( 1 ) {
    if ( rtems_rate_monotonic_period( periods[i], period ) == RTEMS_TIMEOUT ) {
      printf( "missed period. task %d.\n", i );
      break;
    }
                
    lock = rtems_semaphore_obtain( sid[1], RTEMS_WAIT, RTEMS_NO_TIMEOUT );
    printf( "U%d,%d;%d\n", counter, i, unlock );
    printf( "L%d,%d;%d\n", counter, i, lock );
    for ( int j = 0; j < 1000000; j++ ) {
       asm volatile( "nop" );
    }
    counter =  counter + 1;
    unlock = rtems_semaphore_release( sid[1] );
                
    //printf( "release: %s\n", rtems_status_text( status ) );
    //printf( "U;%d\n", status );
    //printf( "Task %d:N P:%d\n", i, get_priority_self() );
  }
        
  status = rtems_rate_monotonic_delete ( periods[i] );
  if ( status != RTEMS_SUCCESSFUL ) {
    printf( "rtems_rate_monotonic_delete failed with status of %d.\n", status );
  }
  status = rtems_task_delete( RTEMS_SELF );    /* should not return */
  printf( "rtems_task_delete returned with status of %d.\n", status );
}

rtems_task task_entry2(
  rtems_task_argument i
)
{
  //printf( "Task %d started\n", i );
  rtems_name name;
  rtems_status_code status;
  name = rtems_build_name( 'P', 'E', 'R', '0' + i );
  status = rtems_rate_monotonic_create( name, &periods[i] );
  //printf( "create monotonic: %d: %s\n", i, rtems_status_text( status ) );
  int period;
  period = priorities[i];
  period = period * 15;
        
  while ( 1 ) {
    if ( rtems_rate_monotonic_period( periods[i], period ) == RTEMS_TIMEOUT ) {
      printf( "missed period. task %d.\n", i );
      break;
    }
    status = rtems_semaphore_obtain( sid[2], RTEMS_WAIT, RTEMS_NO_TIMEOUT );
    //printf( "L;%d\n", status );
    for ( int j = 0; j < 1000000; j++ ) {
      asm volatile( "nop" );
    }
    status = rtems_semaphore_release( sid[2] );
    //printf( "release: %s\n", rtems_status_text( status ) );
    //printf( "U;%d\n", status);
    //printf( "Task %d:N P:%d\n", i, get_priority_self() );
  }
        
  status = rtems_rate_monotonic_delete( periods[i] );
  if ( status != RTEMS_SUCCESSFUL ) {
    printf( "rtems_rate_monotonic_delete failed with status of %d.\n", status );
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
  result = rtems_object_get_name( id, sizeof ( buffer ), buffer );
  printk( "ID=0x%08x name=%s\n", id, ( ( result ) ? result : "no name" ) );
}

