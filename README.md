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

# Protocol Tests:
Test suites for DPCP, MPCP, FMLP, DFLP, and beta version of HDGA.

# PowerPC Deployment:
We support the deployment of RTEMS on T4240rdb board with powerpc architecture.<br />
The compilation of RTEMS is based on the guide: [T4240RDB Deployment Guide](https://es-rtos-kh.blogspot.com/2018/10/rtemsqoriq-how-to-deploy-rtems-5-on-nxp.html).<br />
The deployment details can be found in 'Deploy to T4240rdb'.<br />
We also provide the template file of t4240rdb.dtb.<br />

# RTEMS-5 Support:
We support aforementationed protocols for official release of RTEMS-5.1 (in folder RTEMS-5). In addition, the implementation for DGA has been formally verified (by Surya Subramanian).
<br />
## Protocols Support:
The patch `RTEMS_file.patch` can be applied to the downloaded RTEMS-5.1, and enter the `rtems` folder, by executing `patch -p1 < RTEMS_file.patch`.
<br />
The compilation of RTEMS based on qemu can refer to [RTEMS Compilation Guide](https://es-rtos-kh.blogspot.com/2020/06/rsbrtems-5-with-qemu-smp.html).
<br />
## Formal Verification:
The detailed deployment for verification can refer to [Protocol_Verification](https://github.com/JJShi92/Resource-Synchronization-Protocols-Verification-RTEMS). The detailed steps are as follows:
1. RTEMS Installation:
   1. RBS Build:
      1. `git clone git://git.rtems.org/rtems-source-builder.git rsb`
      2. Enter the `rsb/rtems` folder and execute `../source-builder/sb-set-builder --prefix=/home/YOUR_DIC/build/. 5/rtems-powerpc`
      3. Export to your path: add `export PATH=$PATH:~/YOUR_DIC/build/bin` in the end of file `.bashrc` in your home directory, and execute `source ~/.bashrc`.
   2. RTEMS Build:
      1. `git clone git://git.rtems.org/rtems.git`, and apply the patch file.
      2. Enter `rtems` folder and execute `./bootstrap`.
      3. Create a new folder `mkdir rtems-build` to store built files.
      4. Enter the `rtems-build` and execute `../rtems/configure --target=powerpc-rtems5 --enable-rtemsbsp=qoriq_e6500_32 --enable-smp --enable-tests=yes --enable-debug --prefix=/home/YOUR_DIC/rtems-build/`.
      5. Build the RTEMS `make install`.
```
├──  Home
│   ├──  RTEMS
│   │   ├──  rsb
│   │   │     ├──   bare
│   │   │     ├──   rtems
│   │   │     ├──    source-builder
│   │   ├──  rtems
|   |   ├──  build
|   |   ├──  rtems-build
``` 
2. Install Frama-C via `opam`, our verification is supported by Frama-C.25.0. Detailed installation guide can be found in [Protocol_Verification](https://github.com/JJShi92/Resource-Synchronization-Protocols-Verification-RTEMS).
3. Verification Deployment:
