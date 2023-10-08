# RTEMS-Resource-Synchronization-Protocols
The patch for supporting multiprocessor resource synchronization protocols on RTEMS.
<br />
protocol_tests are some test cases that can be used to verify the features of different protocols.
<br />
# RTEMS-4:
## Supported Protocols:
DPCP, MPCP, FMLP, DFLP, and beta version of HDGA.
<br />
## HowTo:
This patch is based on the original RTEMS from commit c1a1f2c8da4993b03f0a8fadac8f0521df48abec.
<br />
Please download the RTEMS from its original release site (https://github.com/RTEMS/rtems), and then apply our patch.

        patch -p1 < RTEMS_patch_resource_protocols.patch

<br />
# Protocol tests:
Test suites for DPCP, MPCP, FMLP, DFLP, and beta version of HDGA.

# PowerPC Deployment:
We support the deployment of RTEMS on T4240rdb board with powerpc architecture.<br />
The compilation of RTEMS is based on the guide: [T4240RDB Deployment Guid](https://es-rtos-kh.blogspot.com/2018/10/rtemsqoriq-how-to-deploy-rtems-5-on-nxp.html).<br />
The deployment details can be found in 'Deploy to T4240rdb'.<br />
We also provide the template file of t4240rdb.dtb.<br />

# RTEMS-5 Support:
We support aforementationed protocols for RTEMS-5 (in folder RTEMS-5). In addition, the implementation for DGA has been formally verified (by Surya Subramanian).
<br />
The detailed deployment for verification can refer to [Protocol_Verification](https://github.com/JJShi92/Resource-Synchronization-Protocols-Verification-RTEMS)
