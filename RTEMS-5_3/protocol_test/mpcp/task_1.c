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
    uint32_t cpu;
    rtems_status_code status;

    printf("Starting TAS1: \n");

    /* Print that task is running and the cpu number */
    cpu = rtems_scheduler_get_processor();
    printf("TAS1 running on CPU %" PRIu32 "\n", cpu);
    assert(cpu==1);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore1, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TAS1 obtaining SEM1\n");
    assert(status==0);
    wait(200);

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore1);
    printf("TAS1 releasing SEM1\n");
    assert(status==0);
    wait(100);

    /* End of TAS1 */
    printf("End of TAS1\n");
    rtems_task_suspend(RTEMS_SELF);
}