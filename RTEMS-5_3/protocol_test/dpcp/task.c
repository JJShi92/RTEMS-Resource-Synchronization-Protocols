#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <tmacros.h>
#include "system.h"


rtems_task Test_task(
    rtems_task_argument arg
) 
{
    uint32_t cpu_application;
    uint32_t cpu_synchronization;
    rtems_status_code status;

    /* Print that task is running and the cpu number */
    cpu_application = rtems_scheduler_get_processor();
    locked_printf("Task running on CPU %" PRIu32 "\n", cpu_application);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    directive_failed(status, "rtems_semaphore_obtain\n");

    cpu_synchronization = rtems_scheduler_get_processor();
    locked_printf("Obtained semaphore. Task running on CPU %" PRIu32 "\n", cpu_synchronization);
    rtems_test_assert(cpu_application != cpu_synchronization);

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore);
    directive_failed(status, "rtems_semaphore_release\n");

    cpu_application = rtems_scheduler_get_processor();
    locked_printf("Released semaphore. Task running on CPU %" PRIu32 "\n", cpu_application);
    rtems_test_assert(cpu_application != cpu_synchronization);
}