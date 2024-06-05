# RTEMS-Resource-Synchronization-Protocols
The patch for supporting multiprocessor resource synchronization protocols on RTEMS.
<br />
protocol_tests are some test cases that can be used to verify the features of different protocols.
<br />
# RTEMS-4:
## Supported Protocols:
DPCP, MPCP, FMLP, DFLP, and beta version of HDGA.
<br />
## How-to:
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

# RTEMS-5.1 Support:
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
   The folder structure is as follows:
    
   ```
   ├──  Home
   │   ├──  RTEMS
   │   │   ├──  rsb
   │   │   ├──  rtems
   |   |   ├──  build
   |   |   ├──  rtems-build
   ``` 
2. Install Frama-C via `opam`, our verification is supported by Frama-C.25.0. Detailed installation guide can be found in [Protocol_Verification](https://github.com/JJShi92/Resource-Synchronization-Protocols-Verification-RTEMS).
3. Verification Deployment:
   1. Add all the function contracts in the location `/Home/YOUR_DIR/rtems/cpukit/ directory`.
   2. Due to the limited support for C11 of Frama-C, the following files in `/Home/YOUR_DIR/rtems/cpukit/include/rtems/score/` have to be adjusted:
      | File | Original code | Updated Code |
      | ------ | ------ | ----- |
      | cpustdatomic.h | Line number 45 and 46 | Replace Line 45 & 46 with `#include <rtems/score/isrlevel.h>`|
      | threadq.h | Line number 399  | Remove RTEMS_ZERO_LENGTH_ARRAY in array size |
      | thread.h  | Line number 889 | Remove RTEMS_ZERO_LENGTH_ARRAY in array size |
      | percpu.h  | Line number 236 | Add `int x;` after typedef struct { |
   3. Enter the folder `/home/YOUR_DIC/rtems/cpukit/` and execute `eval $(opam env)`
   4. The following command is applied to lunch the DGA verification in Frama-C:
      ```
      frama-c-gui -cpp-command '/home/YOUR_DIC/build/bin/powerpc-rtems5-gcc -C -E \
      -I./include -I./score/cpu/powerpc/include/ \
      -I/home/YOUR_DIC/rtems-build/powerpc-rtems5/c/qoriq_e6500_32/include/ \
      -I/home/YOUR_DIC/build/lib/gcc/powerpc-rtems5/7.5.0/include \
      -I/home/YOUR_DIC/build/powerpc-rtems5/include \
      -nostdinc -include hdga_contracts_t.h' -machdep ppc_32 -cpp-frama-c-compliant -c11       include/rtems/score/hdgaimpl.h
      ```


# RTEMS-5.3 Support:
## Supported Protocols:
DPCP, MPCP

## How-to: 
The RTEMS-5.3 Patch is based on the 5.3 tag from the original RTEMS source(http://github.com/RTEMS/rtems). To download the source using git run:

      git clone https://github.com/RTEMS/rtems.git
      cd rtems
      git checkout tags/5.3

then apply the patch from the `RTEMS-5_3` folder:

      patch -p1 < RTEMS_patch_DPCP_MPCP.patch

## Test suites:
Test suites for DPCP and MPCP on RTEMS-5.3 can be found in `protocol_test` inside the `RTEMS-5_3` folder. 

## Formal Verification:
Verifications are provided for both DPCP and MPCP in the `RTEMS-5_3/verifications` directory.  