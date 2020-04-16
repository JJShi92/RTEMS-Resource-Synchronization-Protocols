#ifndef SYSTEM_H_
#define SYSTEM_H_

#include <bsp.h> /* for device driver prototypes */
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER
#define CONFIGURE_MAXIMUM_TASKS 18
#define CONFIGURE_MAXIMUM_PROCESSORS 4 
#define CONFIGURE_MAXIMUM_PRIORITY 255
#define CONFIGURE_INIT_TASK_NAME rtems_build_name( 'I', 'N', 'I', 'T' )
#define CONFIGURE_MAXIMUM_SEMAPHORES        4 
#define CONFIGURE_MAXIMUM_DFLPL_SEMAPHORES 4
#define CONFIGURE_MAXIMUM_FMLPL_SEMAPHORES        4 
#define CONFIGURE_MAXIMUM_MRSP_SEMAPHORES        4 
#define CONFIGURE_MAXIMUM_PERIODS           18
#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_INIT
#define CONFIGURE_EXTRA_TASK_STACKS         (3 * RTEMS_MINIMUM_STACK_SIZE)
rtems_task init(rtems_task_argument argument);
#define CONFIGURE_INIT_TASK_ENTRY_POINT init

/* Configuration Step 1 - Scheduler Algorithms */
#define CONFIGURE_SCHEDULER_PRIORITY_SMP
#include <rtems/scheduler.h>

/* Configuration Step 2 - Schedulers */
RTEMS_SCHEDULER_PRIORITY_SMP(sched0, 256);
RTEMS_SCHEDULER_PRIORITY_SMP(sched1, 256);
RTEMS_SCHEDULER_PRIORITY_SMP(sched2, 256);
RTEMS_SCHEDULER_PRIORITY_SMP(sched3, 256);

/* Configuration Step 3 - Scheduler Table */
#define CONFIGURE_SCHEDULER_TABLE_ENTRIES \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP( \
    sched0, \
    rtems_build_name('S', 'C', 'D', '0') \
  ), \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP( \
    sched1, \
    rtems_build_name('S', 'C', 'D', '1') \
  ), \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP( \
    sched2, \
    rtems_build_name('S', 'C', 'D', '2') \
  ), \
  RTEMS_SCHEDULER_TABLE_PRIORITY_SMP( \
    sched3, \
    rtems_build_name('S', 'C', 'D', '3') \
  )

/* Configuration Step 4 - Processor to Scheduler Assignment */
#define CONFIGURE_SCHEDULER_ASSIGNMENTS \
  RTEMS_SCHEDULER_ASSIGN(0, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY), \
  RTEMS_SCHEDULER_ASSIGN(1, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY), \
  RTEMS_SCHEDULER_ASSIGN(2, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY), \
  RTEMS_SCHEDULER_ASSIGN(3, RTEMS_SCHEDULER_ASSIGN_PROCESSOR_MANDATORY)


#include <rtems/confdefs.h>
#endif /* SYSTEM_H_ */
