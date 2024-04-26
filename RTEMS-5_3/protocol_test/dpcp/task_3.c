#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "system.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>   

rtems_task Test_task_3(
    rtems_task_argument arg
) 
{
    uint32_t cpu_application;
    uint32_t cpu_synchronization;
    uint32_t cpu_return;
    rtems_status_code status;
    rtems_id task_2_id;
    
    printf("Starting TAS3: \n");

    /* Print that task is running and the cpu number */
    cpu_application = rtems_scheduler_get_processor();
    printf("TAS3 running on CPU %" PRIu32 "\n", cpu_application);
    assert(cpu_application==1);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore2, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TA3 obtaining SEM2\n");
    assert(status==0);
    wait(100);

    /* Check that task migrated */
    cpu_synchronization = rtems_scheduler_get_processor();
    printf("TAS3 running on CPU %" PRIu32 "\n", cpu_synchronization);
    if(cpu_application == cpu_synchronization)
    {
        printf("TA3 failed to migrate to synchronization CPU. Test failed.\n");
        exit(1);
    }

    /* Continue running until TA2 is suspended */
    status = rtems_task_ident(rtems_build_name( 'T', 'A', 'S', '2' ), RTEMS_SEARCH_ALL_NODES, &task_2_id);
    assert(status==0);
    while(rtems_task_is_suspended(task_2_id) == RTEMS_SUCCESSFUL) {continue;}
    printf("End of TAS3.\n");

    /* TA3 is last task so call exit. */
    exit(0);
}