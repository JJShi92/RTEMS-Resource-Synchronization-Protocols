# RTEMS-Resource-Synchronization-Protocols
The patch for supporting multiprocessor resource synchronization protocols on RTEMS.
<br />
protocol_tests are some test cases that can be used to verify the features of different protocols.
<br />
# Supported Protocols:
DPCP, MPCP, FMLP, DFLP, and beta version of HDGA.
<br />
# HowTo:
This patch is based on the original RTEMS from commit c1a1f2c8da4993b03f0a8fadac8f0521df48abec.
<br />
Please download the RTEMS from its original release site (https://github.com/RTEMS/rtems), and then apply our patch.

        patch -p1 < RTEMS_patch_resource_protocols.patch

<br />
If you want to deploy the RTEMS to T4240RDB board, you can follow the guide 'Deploy to T4240rdb'.

# RTEMS-5 Support:
We support aforementationed protocols for RTEMS-5 (in folder RTEMS-5). In addition, the implementation for DGA has been formally verified (by Surya Subramanian).
<br />
The detailed deployment for verification can refer to [Protocol_Verification](https://github.com/JJShi92/Resource-Synchronization-Protocols-Verification-RTEMS)
