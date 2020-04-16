#define CONFIGURE_INIT
#define CONFIGURE_MAXIMUM_USER_EXTENSIONS 1
#include "system.h"
#include "stdio.h"
#include <assert.h>

rtems_id sid;   // Semaphore ID
rtems_id task1; // ID of Task1
rtems_id task2; // ID of Task2
rtems_id task3; // ID of Migration Task
rtems_id main; // ID of Migration Task
rtems_id block;
rtems_status_code rsc; //tmp variable for status code
rtems_id scheds[3]; //scheduler ids
rtems_id schid;

rtems_task task1_entry( rtems_task_argument argument );
rtems_task task2_entry( rtems_task_argument argument );
rtems_task task3_entry( rtems_task_argument argument );
rtems_task main_entry( rtems_task_argument argument );
rtems_task block_entry( rtems_task_argument argument );
void print_name( rtems_id id );
void init_sched();

void init_sched () {
  uint32_t cpu_index;
  printf( "PROCESSOR COUNT: %d\n",rtems_get_processor_count() );
  for ( cpu_index = 0; cpu_index < 2; cpu_index++ ) {
    rsc = rtems_scheduler_ident_by_processor( cpu_index, &scheds[cpu_index] );
    printf("rtems_scheduler_by_processor( %d, &scheds[%d] ): %s\n", cpu_index,cpu_index, rtems_status_text ( rsc ) );
    printf("%d\n",scheds[cpu_index]);
  }
}

rtems_task init(
rtems_task_argument argument
)
{
  printf( "TEST START:\n" );
  init_extensions ();
  /* Getting the scheduler instance ids of the processors */
  init_sched ();

  /* Normal Task: */
  rsc = rtems_task_create(
    rtems_build_name( 'B', 'L', 'O', 'C' ), 
    2,
    RTEMS_MINIMUM_STACK_SIZE, RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &block
  );

  printf( "Create normal task: %s\n", rtems_status_text( rsc ) );

  rsc = rtems_task_create (
    rtems_build_name( 'T', 'A', 'S', '1' ),
    2,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &task1
  );

  printf("Create normal task: %s\n", rtems_status_text( rsc ) );

  rsc = rtems_task_create (
    rtems_build_name( 'T', 'A', 'S', '2' ),
    69,
    RTEMS_MINIMUM_STACK_SIZE, 
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT,
    &task2
  );

  /* This task migrates too, but only after migr2 migr1 are done, with their execution: */
  printf("Create normal task2: %s\n", rtems_status_text(rsc));

  /* Create the task that migrates: */
  rsc = rtems_task_create(
    rtems_build_name( 'T', 'A', 'S', '3' ),
    5,
    RTEMS_MINIMUM_STACK_SIZE, 
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT, 
    &task3
  );

  /* Create the task that migrates: */
  rsc = rtems_task_create(
    rtems_build_name ('M', 'A', 'I', 'N'), 2,
    TEMS_MINIMUM_STACK_SIZE, 
    RTEMS_PREEMPT,
    RTEMS_NO_FLOATING_POINT,
    &main
  );

  printf( "Create migration task: %s\n", rtems_status_text( rsc ) );
  /* Create the DPCP Semaphore */

  /*
  rsc = rtems_semaphore_create (
    rtems_build_name ('D', 'F', 'L', 'P'), 1,
    (RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_FLEXIBLE_LOCKING_LONG | RTEMS_GLOBAL), 
    1, 
    &sid
  );
  printf( "Create DFLPL Semaphore: %s\n", rtems_status_text( rsc ) );
  */

  rsc = rtems_semaphore_create (
    rtems_build_name ('D', 'F', 'L', 'P'), 
    1,
    (RTEMS_BINARY_SEMAPHORE | RTEMS_FLEXIBLE_MULTIPROCESSOR_LOCKING_LONG | RTEMS_FIFO | RTEMS_GLOBAL), 
    1,
    &sid);
    printf("Create FMLPL Semaphore: %s\n", rtems_status_text( rsc ) 
  );

  /*migr and task1 on p1*/
  rtems_task_set_scheduler( task1, scheds[0], 69 );
  rtems_task_set_scheduler( task2, scheds[0], 12 );
  rtems_task_set_scheduler( task3, scheds[0], 5 );
  rtems_task_set_scheduler( main, scheds[0], 65 );
  rtems_task_set_scheduler( block, scheds[1], 22 );

  rtems_task_get_scheduler( task1, &sh );
  printf( "Scheduler task1: %d\n", sh );
  rtems_task_get_scheduler( task2, &sh );
  printf( "Scheduler task2: %d\n", sh );
  rtems_task_get_scheduler( task3, &sh );
  printf( "Scheduler task3: %d\n", sh );
  rtems_task_get_scheduler( main, &sh );
  printf( "Scheduler main: %d\n", sh );
  rtems_task_get_scheduler( block, &sh );
  printf( "Scheduler block: %d\n", sh );

  rtems_task_start( main, main_entry, 0 );
  rtems_task_start( block, block_entry, 0 );
  rtems_task_delete ( RTEMS_SELF );    /* should not return */
}

rtems_task block_entry(
  rtems_task_argument argument
)
{  
  printf("block START\n");  

  for ( int j = 0; j < 20; j++ ) {
    for ( int i = 0; i < 20008889; i++ ) {
      asm volatile("nop"::);
    }
  }

  rtems_task_start( task3, task3_entry, 0 );
  for ( int j = 0; j < 20; j++ ) {
      for (int i = 0; i < 200038889; i++ ) {
        asm volatile ("nop"::);
    }
  }
  
  printf( "block END\n" );  
  rtems_task_suspend(RTEMS_SELF);
}



/*task1 task*/
rtems_task task1_entry(
  rtems_task_argument argument
)
{  
  printf("task1 START\n");  

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 200089; i++) {
      asm volatile ("nop"::);
    }
  }

  printf("task1: Obtaining semaphore: sid\n");				
  rsc = rtems_semaphore_obtain(sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT);                     

  for(int j = 0; j < 20; j++) {
      for (int i = 0; i < 20000000; i++) {
        asm volatile ("nop"::);
    }
  }

  rsc = rtems_semaphore_release( sid ); 
  
  printf( "task1: Releasing semaphore: sid2 \n" );
  printf( "task1 END\n" );  
  rtems_task_suspend(RTEMS_SELF);
}

/*task2 task*/
rtems_task task2_entry(
  rtems_task_argument argument
)
{
  printf("task2 START\n");  
  /*obtaining the DPCP sempahore, migrating to p2*/
  printf("task2: Obtaining semaphore: sid\n");	
  rsc = rtems_semaphore_obtain(sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT);                     

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
        asm volatile ("nop"::);
    }
  }

  rsc = rtems_semaphore_release(sid); 
  printf("task2: Releasing semaphore: sid \n");
  printf("task2 END\n");  

  rtems_task_suspend(RTEMS_SELF);
}

/*migr task*/
rtems_task main_entry(
  rtems_task_argument argument
)
{
  printf( "main START\n" );
  printf( "main: Obtaining semaphore: sid\n" );					
  rtems_semaphore_obtain( sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT );                     

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
      asm volatile ("nop"::);
    }
  }
  //rtems_task_start(task3, task3_entry, 0);

  for ( int j = 0; j < 20; j++ ) {
    for ( int i = 0; i < 20000000; i++ ) {
      asm volatile ("nop"::);
    }
  }
  rtems_task_start( task2, task2_entry, 0 );

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
      asm volatile ("nop"::);
    }
  }
  rtems_task_start(task1, task1_entry, 0);

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
        asm volatile ("nop"::);
    }
  }

  printf( "main: Releasing semaphore: sid \n");
  rtems_semaphore_release( sid );          
  printf( "main END\n" );
  rtems_task_suspend( RTEMS_SELF );
}

/*task3 task*/
rtems_task task3_entry(
  rtems_task_argument argument
)
{
  printf("task3 START\n");  

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 200089; i++) {
      asm volatile ("nop"::);
    }
  }
  
  printf("task3: Obtaining semaphore: sid\n");					/*obtaining the DPCP sempahore, migrating to p2*/
  rsc = rtems_semaphore_obtain(sid, RTEMS_WAIT, RTEMS_NO_TIMEOUT);                     

  for(int j = 0; j < 20; j++) {
    for (int i = 0; i < 20000000; i++) {
      asm volatile ("nop"::);
    }
  }

  rsc = rtems_semaphore_release( sid ); 
  printf( "task3: Releasing semaphore: sid2 \n" );
  printf( "task3 END\n" );  
  rtems_task_suspend( RTEMS_SELF );
}

void print_name(rtems_id id)
{
  char  buffer[10];   /* name assumed to be 10 characters or less */
  char *result;
  result = rtems_object_get_name( id, sizeof(buffer), buffer );
  printk( "ID=0x%08x name=%s\n", id, ((result) ? result : "no name") );
}

