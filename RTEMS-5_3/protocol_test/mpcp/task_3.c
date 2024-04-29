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
    uint32_t cpu;
    rtems_status_code status;
    rtems_id id;

    printf("Starting TAS3: \n");

    /* Print that task is running and the cpu number */
    cpu = rtems_scheduler_get_processor();
    printf("TAS3 running on CPU %" PRIu32 "\n", cpu);
    assert(cpu==0);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore2, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TAS3 obtaining SEM2\n");
    assert(status==0);
    wait(300);

    /* Resume TAS2 */
    status = rtems_task_ident(rtems_build_name('T', 'A', 'S', '2'), RTEMS_SEARCH_ALL_NODES, &id);
    assert(status==0);
    status = rtems_task_resume(id);
    assert(status==0);

    /* Wait until TAS1 is finished */
    status = rtems_task_ident(rtems_build_name('T', 'A', 'S', '1'), RTEMS_SEARCH_ALL_NODES, &id);
    assert(status==0);
    while(rtems_task_is_suspended(id) == RTEMS_SUCCESSFUL) {continue;}

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore2);
    printf("TAS3 releasing SEM2\n");
    assert(status==0);
    wait(100);

    /* End of TAS3 */
    printf("End of TAS3\n");
    rtems_task_suspend(RTEMS_SELF);
}