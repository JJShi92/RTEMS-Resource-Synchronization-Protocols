#define CONFIGURE_INIT
#define CONFIGURE_MAXIMUM_USER_EXTENSIONS 1
#include "system.h"
#include "stdio.h"
#include <assert.h>

rtems_id sid1;  // Semaphore ID
rtems_id sid2;  // Semaphore ID
rtems_id task1; // ID of Task1
rtems_id task2; // ID of Task2
rtems_id migr1; // ID of Migration Task
rtems_id migr2; // ID of Migration Task
rtems_status_code rsc; //tmp variable for status code
rtems_id scheds[2]; //scheduler ids
rtems_id schid;

rtems_task task1_entry( rtems_task_argument argument );
rtems_task task2_entry( rtems_task_argument argument );
rtems_task migr1_entry( rtems_task_argument argument );
rtems_task migr2_entry( rtems_task_argument argument );

void print_name( rtems_id id );
void init_sched();
void init_sched(
)
{
  uint32_t cpu_index;
  printf( "PROCESSOR COUNT: %d\n",rtems_get_processor_count() );
  for ( cpu_index = 0; cpu_index < 2; cpu_index++ ) {
    rsc = rtems_scheduler_ident_by_processor(cpu_index, &scheds[cpu_index]);
    printf( "rtems_scheduler_by_processor(%d, &scheds[%d]): %s\n", cpu_index,cpu_index, rtems_status_text( rsc ) );
    printf( "%d\n",scheds[cpu_index] );
  }
}

rtems_task init(
rtems_task_argument argument
)
{
  rtems_id sh;
  printf( "TEST START:\n" );
  /* Getting the scheduler instance ids of the processors */
  init_sched();

  /* Normal Task: */
  rsc = rtems_task_create(
    rtems_build_name('T', 'A', 'S', '1'),
    2,
    RTEMS_MINIMUM_STACK_SIZE, 
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &task1
  );

  printf( "Create normal task: %s\n", rtems_status_text( rsc ) );
  
  rsc = rtems_task_create(rtems_build_name( 'T', 'A', 'S', '2' ), 
    69,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &task2
  );

  /* This task migrates too, but only after migr2 migr1 are done, with their execution: */
  printf( "Create normal task2: %s\n", rtems_status_text( rsc ) );
  
  /* Create the task that migrates: */
  rsc = rtems_task_create(
    rtems_build_name('M', 'I', 'G', 'R'),
    1,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &migr1
  );
    
  /* Create the task that migrates: */
  rsc = rtems_task_create(
    rtems_build_name( 'M', 'I', 'G', 'S' ), 
    8,
    RTEMS_MINIMUM_STACK_SIZE, RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &migr2
  );

  printf( "Create migration task: %s\n", rtems_status_text( rsc ) );
  /* Create the DPCP Semaphore */

  rsc = rtems_semaphore_create(
    rtems_build_name( 'D', 'P', 'C', 'P' ),
    1,
    (RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL), 
    1,
    &sid1
  );
  printf( "Create DPCP Semaphore: %s\n", rtems_status_text( rsc ) );
  
  rsc = rtems_semaphore_create(
    rtems_build_name( 'D', 'P', 'C', 'Q' ), 
    1,
    (RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL), 
    7, 
    &sid2
  );
  printf( "Create DPCP Semaphore: %s\n", rtems_status_text( rsc ) );
  
  /*migr and task1 on p1*/
  rtems_task_set_scheduler( task1, scheds[0], 69 );
  rtems_task_set_scheduler( migr1, scheds[0], 12 );
  rtems_task_set_scheduler( task2, scheds[0], 42 );
  rtems_task_set_scheduler( migr2, scheds[0], 8 );
  
  rtems_task_start( task2, task2_entry, 0);
  rtems_task_start( migr2, migr2_entry, 0);
  rtems_task_start( task1, task1_entry, 0);  
  rtems_task_start( migr1, migr1_entry, 0);
  
  printf( "INIT COMPLETE\n" );
  rsc = rtems_task_delete( RTEMS_SELF );    /* should not return */
}

/*task1 task*/
rtems_task task1_entry(
rtems_task_argument argument
)
{  
  while ( 1337>69 ) {
    for ( int j = 0; j < 20; j++ ) {
      for ( int i = 0; i < 20000000; i++ ) {
        asm volatile ("nop"::);
      }
    }
  }
  rtems_task_suspend( RTEMS_SELF );
}

/*task2 task*/
rtems_task task2_entry(
rtems_task_argument argument
)
{
  printf("task2 START\n");  
  
  /*obtaining the DPCP sempahore, migrating to p2*/
  printf( "task2: Obtaining semaphore: sid2\n" );		
  rsc = rtems_semaphore_obtain( sid2, RTEMS_WAIT, RTEMS_NO_TIMEOUT );                     

  for( int j = 0; j < 20; j++ ) {
    for ( int i = 0; i < 20000000; i++ ) {
      asm volatile ("nop"::);
    }
  }

  rsc = rtems_semaphore_release( sid2 ); 
  printf("task2: Releasing semaphore: sid2 \n");
  
  /*obtaining the DPCP sempahore, migrating to p2*/
  printf("task2: Obtaining semaphore: sid2\n");				
  rsc = rtems_semaphore_obtain(sid2, RTEMS_WAIT, RTEMS_NO_TIMEOUT);                     

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
      asm volatile ("nop"::);
    }
  }

  rsc = rtems_semaphore_release( sid2 ); 
  printf( "task2: Releasing semaphore: sid2 \n" );
  printf( "task2 END\n" );  
  rtems_task_suspend(RTEMS_SELF);
}

/*migr task*/
rtems_task migr1_entry(
rtems_task_argument argument
)
{
  printf( "migr1 START\n" );
  printf( "migr1 current processor before obtaining semaphore sid1: %d\n", rtems_get_current_processor() );
  printf( "migr1: Obtaining semaphore: sid1\n" );					/*obtaining the DPCP sempahore, migrating to p2*/
  rtems_semaphore_obtain( sid1, RTEMS_WAIT, RTEMS_NO_TIMEOUT );                     

  for ( int j = 0; j < 20; j++ ) {
    for ( int i = 0; i < 20000000; i++ ) {
      asm volatile("nop"::);
    }
  }
  printf( "migr1 current processor after obtaining semaphore sid1: %d\n", rtems_get_current_processor() );
  /*releasing the DPCP semphore, migrating back to p1*/
  rtems_semaphore_release( sid1 );                     
  printf( "migr1: Releasing semaphore: sid1 \n" );
  printf( "migr1 current processor after releasing semaphore sid1: %d\n",rtems_get_current_processor() );
  printf( "migr1 END\n" );
  rtems_task_suspend( RTEMS_SELF );
}

/*migr task*/
rtems_task migr2_entry(
rtems_task_argument argument
)
{
  printf( "migr2 START\n" );
  printf( "migr2 current processor before obtaining semaphore sid2: %d\n", rtems_get_current_processor() );
  
  /*obtaining the DPCP sempahore, migrating to p2*/
  printf("migr2: Obtaining semaphore: sid2\n");					
  rsc = rtems_semaphore_obtain(sid2, RTEMS_WAIT, RTEMS_NO_TIMEOUT);                     

  for ( int j = 0; j < 20; j++ ) {
    for ( int i = 0; i < 20000000; i++ ) {
      asm volatile("nop"::);
    }
  }
  printf( "migr2 current processor after obtaining semaphore sid2: %d\n", rtems_get_current_processor() );
  /*releasing the DPCP semphore, migrating back to p1*/
  rsc = rtems_semaphore_release( sid2 );                         
  printf( "migr2: Releasing semaphore: sid2 \n" );
  printf( "migr2 current processor after releasing semaphore sid2: %d\n",rtems_get_current_processor() );
  printf( "migr2 END\n");
  rtems_task_suspend(RTEMS_SELF);
}

void print_name(
rtems_id id
)
{
  char  buffer[10];   /* name assumed to be 10 characters or less */
  char *result;
  result = rtems_object_get_name( id, sizeof(buffer), buffer );
  printk( "ID=0x%08x name=%s\n", id, ((result) ? result : "no name") );
}

