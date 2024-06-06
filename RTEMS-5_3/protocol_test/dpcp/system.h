#include <bsp.h>

/* Task functions numbered according to relative priority*/

rtems_task Test_task_1(
  rtems_task_argument argument
);

rtems_task Test_task_2(
  rtems_task_argument argument
);

rtems_task Test_task_3(
  rtems_task_argument argument
);

void wait(int ticks);

/* configuration information */

#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER

#define CONFIGURE_MAXIMUM_PROCESSORS 3
#define CONFIGURE_MAXIMUM_PRIORITY 255

#define CONFIGURE_MAXIMUM_TASKS 3
#define CONFIGURE_MAXIMUM_SEMAPHORES 2

#define CONFIGURE_INIT_TASK_PRIORITY 10

#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_INIT_TASK_NAME rtems_build_name( 'T', 'A', 'S', '2' )
#define CONFIGURE_INIT_TASK_ENTRY_POINT Test_task_2

/* Configuration Step 1 - Scheduler Algorithms */
#define CONFIGURE_SCHEDULER_PRIORITY_SMP
#include <rtems/scheduler.h>

/* Configuration Step 2 - Schedulers */
RTEMS_SCHEDULER_PRIORITY_SMP(app1, CONFIGURE_MAXIMUM_PRIORITY + 1);
RTEMS_SCHEDULER_PRIORITY_SMP(app2, CONFIGURE_MAXIMUM_PRIORITY + 1);
RTEMS_SCHEDULER_PRIORITY_SMP(sync, CONFIGURE_MAXIMUM_PRIORITY + 1);

/* Configuration Step 3 - Scheduler Table */
#define CONFIGURE_SCHEDULER_TABLE_ENTRIES \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP(app1, rtems_build_name('A', 'P', 'P', '1')), \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP(app2, rtems_build_name('A', 'P', 'P', '2')), \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP(sync, rtems_build_name('S', 'Y', 'N', 'C'))

/* Configuration Step 4 - Processor to Scheduler Assignment */
#define CONFIGURE_SCHEDULER_ASSIGNMENTS \
  RTEMS_SCHEDULER_ASSIGN(0, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY), \
  RTEMS_SCHEDULER_ASSIGN(1, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY), \
  RTEMS_SCHEDULER_ASSIGN(2, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY)

#include <rtems/confdefs.h>

/* global variables */

rtems_id Semaphore1; /* synchronisation semaphore SEM1 */ 
rtems_id Semaphore2; /* synchronisation semaphore SEM2 */ 
