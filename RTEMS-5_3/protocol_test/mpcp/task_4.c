#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "system.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>   


rtems_task Test_task_4(
    rtems_task_argument arg
)  
{
    uint32_t cpu;
    rtems_status_code status;
    rtems_id id;
    rtems_id scheduler_id;

    printf("Starting TAS4: \n");

    /* Print that task is running and the cpu number */
    cpu = rtems_scheduler_get_processor();
    printf("TAS4 running on CPU %" PRIu32 "\n", cpu);
    assert(cpu==1);

    /* Create and start TAS1 on APP2 scheduler */
    status = rtems_scheduler_ident(rtems_build_name('A', 'P', 'P', '2'), &scheduler_id);
    assert(status==0);
    status = rtems_task_create(
        rtems_build_name('T', 'A', 'S', '1'),
        11,
        RTEMS_MINIMUM_STACK_SIZE,
        RTEMS_DEFAULT_MODES,
        RTEMS_DEFAULT_ATTRIBUTES,
        &id
    );
    assert(status==0);
    status = rtems_task_set_scheduler(id, scheduler_id, 11);
    assert(status==0);
    status = rtems_task_start(id, Test_task_1, 0);
    assert(status==0);

    wait(100);

    /* lock semaphore */
    status = rtems_semaphore_obtain(Semaphore1, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    printf("TAS4 obtaining SEM1\n");
    assert(status==0);
    wait(200);

    /* Release semaphore */
    status = rtems_semaphore_release(Semaphore1);
    printf("TAS4 releasing SEM1\n");
    assert(status==0);
    wait(100);

    /* Wait until TAS3 is finished */
    status = rtems_task_ident(rtems_build_name('T', 'A', 'S', '3'), RTEMS_SEARCH_ALL_NODES, &id);
    assert(status==0);
    while(rtems_task_is_suspended(id) == RTEMS_SUCCESSFUL) {continue;}

    /* End of TAS4. TAS4 is last task so exit */
    printf("End of TAS4\n");
    exit(0);
}