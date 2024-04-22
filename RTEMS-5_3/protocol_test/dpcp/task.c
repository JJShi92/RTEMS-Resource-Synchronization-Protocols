#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "system.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>   


rtems_task Test_task(
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
    status = rtems_semaphore_obtain(Semaphore, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TAS1 obtained SEM1: %s\n", rtems_status_text(status));
    assert(status==0); //RTEMS_SUCCESSFUL
    
    cpu_synchronization = rtems_scheduler_get_processor();
    printf("Obtained semaphore. Task running on CPU %" PRIu32 "\n", cpu_synchronization);
    if(cpu_application == cpu_synchronization)
    {
        printf("Failed to migrate to synchronization CPU. Test failed.\n");
        exit(1);
    }

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore);
    printf("TAS1 releasing semaphore: %s\n", rtems_status_text(status));
    assert(status==0); //RTEMS_SUCCESSFUL

    /* Ensure that task returns to original application processor */
    cpu_return = rtems_scheduler_get_processor();
    printf("Released semaphore. Task running on CPU %" PRIu32 "\n", cpu_return);
    if(cpu_return != cpu_application)
    {
        printf("Failed to migrate from synchronization CPU. Test failed. %" PRIu32 "\n", cpu_return);
        exit(1);
    }

    printf("End of TAS1\n");
    rtems_task_suspend( RTEMS_SELF );
}