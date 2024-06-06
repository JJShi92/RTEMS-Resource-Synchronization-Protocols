#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define CONFIGURE_INIT
#include "system.h"

#include <stdio.h>
#include <assert.h>   
#include <stdlib.h>
#include <inttypes.h>

const char rtems_test_name[] = "DPCP1";

void wait(int ticks)
{
  rtems_interval timeout;
  bool before;

  timeout = rtems_clock_tick_later(ticks);

  do {
    before = rtems_clock_tick_before(timeout);
  } while (before);
}

rtems_task Test_task_2(
  rtems_task_argument argument
)
{
  uint32_t cpu;
  rtems_id id;
  rtems_id scheduler_ids[3];
  rtems_status_code status;
  rtems_task_priority priority;
  
  printf("Starting test: \n");

  /* print id of all schedulers as well as which scheduler is on which processor */
  status = rtems_scheduler_ident(rtems_build_name('A', 'P', 'P', '1'), &scheduler_ids[0]);
  printf("APP1 Scheduler ID %d\n", id);
  assert(status==0);
  status = rtems_scheduler_ident(rtems_build_name('A', 'P', 'P', '2'), &scheduler_ids[1]);
  printf("APP2 Scheduler ID %d\n", id);
  assert(status==0);
  status = rtems_scheduler_ident(rtems_build_name('S', 'Y', 'N', 'C'), &scheduler_ids[3]);
  printf("SYNC Scheduler ID %d\n", id);
  assert(status==0);
  
  status = rtems_scheduler_ident_by_processor(0, &id);
  printf("Processor 0 scheduler ID: %d\n", id);
  assert(status==0);
  status = rtems_scheduler_ident_by_processor(1, &id);
  printf("Processor 1 scheduler ID: %d\n", id);
  assert(status==0);
  status = rtems_scheduler_ident_by_processor(2, &id);
  printf("Processor 2 scheduler ID: %d\n\n", id);
  assert(status==0);

  /*Set TAS2 priority */
  status = rtems_task_set_priority(RTEMS_SELF, 12, &priority);
  assert(status==0);

  /* Output processor */
  cpu = rtems_scheduler_get_processor();
  printf("TAS2 running on CPU %" PRIu32 "\n", cpu);
  assert(cpu==0);

  /* Create global synchronisation semaphores */
  status = rtems_semaphore_create(
    rtems_build_name ('S', 'E', 'M', '1'),
    1,                                             
    RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL,
    1, //Priority 1
    &Semaphore1);
  assert(status==0);
  status = rtems_semaphore_create(
    rtems_build_name ('S', 'E', 'M', '2'),
    1,                                             
    RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL,
    2, //Priority 2
    &Semaphore2);
  assert(status==0);
  status = rtems_semaphore_set_processor(Semaphore1, 2);
  assert(status==0);
  status = rtems_semaphore_set_processor(Semaphore2, 2);
  assert(status==0);

  /* Create and start TAS3 on APP2 scheduler */
  status = rtems_task_create(
    rtems_build_name('T', 'A', 'S', '3'),
    13,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &id
  );
  assert(status==0);
  status = rtems_task_set_scheduler(id, scheduler_ids[1], 13);
  assert(status==0);
  status = rtems_task_start(id, Test_task_3, 0);
  assert(status==0);

  wait(200);

  /* Lock SEM1 */
  status = rtems_semaphore_obtain(Semaphore1, RTEMS_WAIT, 0);
  printf("TAS2 obtaining SEM1\n");
  assert(status==0);

  wait(100);

  /* Check that process moved to sync processor */
  cpu = rtems_scheduler_get_processor();
  printf("TAS2 running on CPU %" PRIu32 "\n", cpu);
  assert(cpu==2);

  /* Create and start TAS */
  status = rtems_task_create(
    rtems_build_name('T', 'A', 'S', '1'),
    11, //priority
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &id
  );
  assert(status==0);

  status = rtems_task_start(id, Test_task_1, 0);
  assert(status==0);
  
  /* Release Semaphore allowing TAS1 to continue */
  status = rtems_semaphore_release(Semaphore1);
  printf("TAS2 releasing SEM1\n");
  assert(status==0);
  wait(100);

  /* Check if process migrated back to application processor */
  cpu = rtems_scheduler_get_processor();
  printf("TAS2 running on CPU %" PRIu32 "\n", cpu);
  assert(cpu==0);

  /* wait until TAS1 is suspended. Should not block TAS1 due to TAS1 having higher priority. */
  while(rtems_task_is_suspended(id) == RTEMS_SUCCESSFUL) {continue;}
  printf("End of TAS2.\n");
  rtems_task_suspend(RTEMS_SELF);
}
