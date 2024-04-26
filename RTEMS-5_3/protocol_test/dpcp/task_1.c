#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "system.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>   


rtems_task Test_task_1(
    rtems_task_argument arg
)  
{
    uint32_t cpu_application;
    uint32_t cpu_synchronization;
    uint32_t cpu_return;
    rtems_status_code status;

    printf("Starting TAS1: \n");

    /* Print that task is running and the cpu number */
    cpu_application = rtems_scheduler_get_processor();
    printf("TAS1 running on CPU %" PRIu32 "\n", cpu_application);
    assert(cpu_application==0);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore1, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TA1 obtaining SEM1\n");
    assert(status==0);
    wait(300);

    /* Check that task migrated*/
    cpu_synchronization = rtems_scheduler_get_processor();
    printf("TAS1 running on CPU %" PRIu32 "\n", cpu_synchronization);
    if(cpu_application == cpu_synchronization)
    {
        printf("TA1 failed to migrate to synchronization CPU. Test failed.\n");
        exit(1);
    }

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore1);
    printf("TAS1 releasing SEM1\n");
    assert(status==0);
    wait(100);

    /* Ensure that task returns to original application processor */
    cpu_return = rtems_scheduler_get_processor();
    printf("TAS1 running on CPU %" PRIu32 "\n", cpu_return);
    if(cpu_return != cpu_application)
    {
        printf("TA1 failed to migrate from synchronization CPU. Test failed.\n");
        exit(1);
    }

    printf("End of TAS1\n");
    rtems_task_suspend( RTEMS_SELF );
}