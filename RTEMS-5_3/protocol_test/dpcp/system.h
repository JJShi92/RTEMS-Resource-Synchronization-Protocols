#include "tmacros.h"
#include "test_support.h"

/* functions */

rtems_task Init(
  rtems_task_argument argument
);

rtems_task Test_task(
  rtems_task_argument argument
);

/* configuration information */

#define CONFIGURE_APPLICATION_DOES_NOT_NEED_CLOCK_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER

#define CONFIGURE_MAXIMUM_PROCESSORS 3 

#define CONFIGURE_MAXIMUM_TASKS 2
#define CONFIGURE_MAXIMUM_SEMAPHORES 1

#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION

#define CONFIGURE_RTEMS_INIT_TASKS_TABLE

#include <rtems/confdefs.h>

/* global variables */

TEST_EXTERN rtems_id Semaphore; /* synchronisation semaphore */ 
