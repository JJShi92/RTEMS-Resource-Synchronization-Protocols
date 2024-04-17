#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define CONFIGURE_INIT
#include "system.h"

#include <stdio.h>
#include <inttypes.h>

const char rtems_test_name[] = "DPCP1";

rtems_task Init(
  rtems_task_argument argument
)
{
  uint32_t          cpu_num;
  rtems_id          id; /* pointer to task thread */
  rtems_status_code status;

  TEST_BEGIN();

  locked_print_initialize();

  if ( rtems_scheduler_get_processor_maximum() < 1 ) {
    locked_printf("More than 1 processor are needed for DPCP.\n");
    TEST_FAILED();
  }

  /* Create/verify global synchronisation semaphore */
  status = rtems_semaphore_create(
    rtems_build_name ('S', 'E', 'M', '1'),
    1,                                             
    RTEMS_GLOBAL                   |
    RTEMS_SIMPLE_BINARY_SEMAPHORE |
    RTEMS_PRIORITY,
    1,
    &Semaphore);
  directive_failed(status, "rtems_semaphore_create\n");

  /* Lock semaphore */
  status = rtems_semaphore_obtain( Semaphore, RTEMS_WAIT, 0);
  directive_failed(status,"rtems_semaphore_obtain of SEM1\n");

  /* Create and start task */
  status = rtems_task_create(
    rtems_build_name('T', 'A', 'S', '1'),
    1,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &id
  )
  directive_failed(status, "rtems_task_create\n");

  status = rtems_task_start(1, Test_task, 1);
  directive_failed(status, "rtems_task_start\n");

  /* Release Semaphore allowing task to continue */
  status = rtems_semaphore_release(Semaphore);
  directive_failed( status,"rtems_semaphore_release\n");
  
  TEST_END();
  rtems_test_exit(0);
}
