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

rtems_task Init(
  rtems_task_argument argument
)
{
  uint32_t          cpu;
  rtems_id          id;
  rtems_status_code status;
  rtems_task_priority priority;
  
  printf("Starting test: \n");

  status = rtems_task_ident(RTEMS_WHO_AM_I, RTEMS_SEARCH_ALL_NODES, &id);
  assert(status==0); //RTEMS_SUCCESSFUL
  status = rtems_task_set_priority(id, 100, &priority);
  printf("Init priority set to 100 from %d: %s\n", priority, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL

  /* print id of all schedulers as well as which scheduler is on which processor */
  status = rtems_scheduler_ident(rtems_build_name('A', 'P', 'P', '1'), &id);
  printf("APP1 Scheduler ID %d: %s\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  status = rtems_scheduler_ident(rtems_build_name('A', 'P', 'P', '2'), &id);
  printf("APP2 Scheduler ID %d: %s\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  status = rtems_scheduler_ident(rtems_build_name('S', 'Y', 'N', 'C'), &id);
  printf("SYNC Scheduler ID %d: %s\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  

  status = rtems_scheduler_ident_by_processor(0, &id);
  printf("Processor 0 scheduler ID: %d: %s\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  status = rtems_scheduler_ident_by_processor(1, &id);
  printf("Processor 1 scheduler ID: %d: %s\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  status = rtems_scheduler_ident_by_processor(2, &id);
  printf("Processor 2 scheduler ID: %d: %s\n\n", id, rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  
  cpu = rtems_scheduler_get_processor();
  printf("Init running on processor %" PRIu32 "\n", cpu);
  assert(cpu==0); //App1 processor
  

  /* Create global synchronisation semaphore */
  status = rtems_semaphore_create(
    rtems_build_name ('S', 'E', 'M', '1'),
    1,                                             
    RTEMS_BINARY_SEMAPHORE | RTEMS_DISTRIBUTED_PRIORITY_CEILING | RTEMS_GLOBAL,
    1,
    &Semaphore);
  printf("Creating SEM1: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL

  status = rtems_semaphore_set_processor(Semaphore, 2);
  printf("Setting SEM1 processor to 2: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL

  /* Lock semaphore */
  status = rtems_semaphore_obtain( Semaphore, RTEMS_WAIT, 0);
  printf("Locking SEM1: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL

  /* Check that process moved to sync processor */
  cpu = rtems_scheduler_get_processor();
  printf("Init running on processor %" PRIu32 "\n", cpu);
  assert(cpu==2);


  /* Create and start task */
  status = rtems_task_create(
    rtems_build_name('T', 'A', 'S', '1'),
    1, //priority 1 = highest
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &id
  );
  printf("creating TAS1: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL

  status = rtems_task_start(id, Test_task, 0);
  printf("Starting TAS1: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  
  /* Release Semaphore allowing TA1 to continue */
  status = rtems_semaphore_release(Semaphore);\
  printf("Releasing SEM1: %s \n", rtems_status_text(status));
  assert(status==0); //RTEMS_SUCCESSFUL
  
  /* Check if process migrated back to application processor */
  cpu = rtems_scheduler_get_processor();
  printf("Init running on processor %" PRIu32 "\n", cpu);
  assert(cpu==0);

  /* wait until TA1 is suspended. Should not block TA1 due to TA1 having higher priority. */
  while(rtems_task_is_suspended(id) == RTEMS_SUCCESSFUL) {continue;}
  printf("End of test.\n");
  exit(0);
}
