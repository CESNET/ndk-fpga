.. _ndk_testing:

NDK testing
-----------

.. warning::

    Attention, this chapter may not be up to date, we are looking for a volunteer to update it.

This chapter describes how the NDK firmware and its HDL components can be tested:

- Test R/W access to scratch registers in the NDK firmware (:ref:`see below <ndk_testing_mi>`).
- Simple HW throughput tests can be executed using the :ref:`Gen Loop Switch (GLS) debug module <gls_debug>` (:ref:`see below <ndk_testing_gls>`).
- HDL components are tested by :ref:`verification using UVM <uvm_ver>` and :ref:`cocotb <cocotb_ver>`.
- There is also a :ref:`simulation of almost the entire firmware using cocotb <cocotb_top_level_sim>`.

.. _ndk_testing_mi:

Testing R/W access to the scratch registers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The NDK firmware implements 64 32-bit scratch registers for testing purposes. Like other parts of the firmware, they are accessible via the :ref:`MI bus <ndk_mi>`. This address space is (among other things) stored in the :ref:`DeviceTree <ndk_devtree>`. The `nfb-bus tool <https://cesnet.github.io/ndk-sw/tools/nfb-bus.html>`_ can be used for easy R/W access to any register in the firmware that is mapped to the MI bus. The following example shows how to:

- obtain or verify the DeviceTree path of the MI TEST SPACE component in the firmware
- read the first scratch register (the offset is 0x0 in the byte format) in the MI TEST SPACE component (selected using the DeviceTree path),
- write a new value (0x42) to it, and
- read it again.

.. code-block:: bash

    $ nfb-bus -l | grep mi_test_space
    $ nfb-bus -p /firmware/mi_pci0_bar0/mi_test_space 0x0
    00000000
    $ nfb-bus -p /firmware/mi_pci0_bar0/mi_test_space 0x0 0x42
    $ nfb-bus -p /firmware/mi_pci0_bar0/mi_test_space 0x0
    00000042

You can test R/W requests to the NDK firmware address space of these scratch registers however you want. Similarly, in the future, you can access the registers in your own application that you build on the NDK platform.

.. _ndk_testing_gls:

GLS module tutorial
^^^^^^^^^^^^^^^^^^^

The NDK firmware may include a GLS module that is instantiated in each DMA stream between the application core and the DMA controller.
This is typical for the ndk-app-minimal reference design (apps/minimal).
The GLS module is used for testing purposes and contains HW packet generators, speed meters, and datapath switches.
Please refer to the :ref:`GLS module documentation <gls_debug>` for a more information.

The GLS module also comes with a Python script (``<NDK-FPGA_root_directory>/comp/mfb_tools/debug/gen_loop_switch/sw/gls_mod.py``) that can be used to quickly perform several basic tests (modes).
For example, you can measure the throughput of the NDK firmware.
A list of test modes can be obtained by running this script th `-h` option.
However, there is a couple of steps that should preceed the usage of this script.

Steps to launch
***************

1. Make sure you have a proper FPGA FW booted, i.e., it contains a GLS module.
You can check this, for example, by issuing ``nfb-bus -l | grep gen_loop_switch`` in the terminal.
The output should be similar to this (more than one instance of GLS may be present):

.. code-block:: text

    $ nfb-bus -l | grep gen_loop_switch
    0x00005000: cesnet,ofm,gen_loop_switch          /firmware/mi_pci0_bar0/dbg_gls0

2. Install the Python OFM package as described in its readme ``ndk-fpga/python/ofm/README.md``.
Do not deactivate the virtual environment.

3. Launch this script by ``python gls_mod.py <options>``.
Add path before the script name if it is not in the current directory.

Usage
*****

See the test modes and other options by running the script with the ``-h`` option:

.. code-block:: text

    $ python gls_mod.py -h
    usage: gls_mod.py [-h] [-d DEVICE] [-i [INDEX]] [-l] [-L] -m {eth_gen,rx,tx,rxtx,dma_rx,dma_tx,dma_rxtx,dma_loop} [-c CHANNELS] [-s MIN MAX STEP] [-R] [-e] [-C TEST_CYCLES] [-f FREQUENCY] [-r {1,2}]

            Uses the GEN_LOOP_SWITCH (SW+FW) module to perform throughput measurements.

    options:
    -h, --help              show this help message and exit
    -d DEVICE, --device DEVICE
                            set the target device; default: 0 (/dev/nfb0)
    -i [INDEX], --index [INDEX]
                            select index(es) of GLS in the Device Tree, e.g.: 0,1; -1 = all available; default: 0
    -l, --log               enable logging to a CSV file
    -L, --log_demo          enable for demo - logs to a TXT file in /tmp directory
    -m {eth_gen,rx,tx,rxtx,dma_rx,dma_tx,dma_rxtx,dma_loop}, --mode {eth_gen,rx,tx,rxtx,dma_rx,dma_tx,dma_rxtx,dma_loop}
                            set the test mode; options:

                            +----------+-----------------------------------------------------------------+
                            | eth_gen  | HW Gen --> TX ETH     ==> RX ETH --> Black Hole; (ETH loopback) |
                            +----------+-----------------------------------------------------------------+
                            | rx       | HW Gen --> TX ETH     ==> RX ETH --> RX DMA;     (ETH loopback) |
                            +----------+-----------------------------------------------------------------+
                            | tx       | TX DMA --> TX ETH     ==> RX ETH --> Black Hole; (ETH loopback) |
                            +----------+-----------------------------------------------------------------+
                            | rxtx     | TX DMA --> TX ETH     ==> RX ETH --> RX DMA;     (ETH loopback) |
                            +----------+-----------------------------------------------------------------+
                            | dma_rx   | HW Gen --> RX DMA     ###                                       |
                            +----------+-----------------------------------------------------------------+
                            | dma_tx   | TX DMA --> Black Hole ###                                       |
                            +----------+-----------------------------------------------------------------+
                            | dma_rxtx | TX DMA --> Black Hole ### HW Gen --> RX DMA;                    |
                            +----------+-----------------------------------------------------------------+
                            | dma_loop | TX DMA --> RX DMA     ### (internal DMA loopback)               |
                            +----------+-----------------------------------------------------------------+

    -c CHANNELS, --channels CHANNELS
                            select the range of Channels used in the test in 'min-max' format; default = all available
    -s MIN MAX STEP, --frame_size MIN MAX STEP
                            set the frame size(s) in bytes (including CRC); default: 64 1518 16
    -R, --repeat            repeat the test until interrupted, otherwise it runs only once
    -e, --ext_loop          force using external loopback instead of PMA loopback (default, only for some modes)
    -C TEST_CYCLES, --test_cycles TEST_CYCLES
                            set the number of test cycles that are averaged for each frame length, default: 4
    -f FREQUENCY, --frequency FREQUENCY
                            set the clock frequency [Hz] at which the APP Core runs; default: 200_000_000
    -r {1,2}, --rate_layer {1,2}
                            measure the rate at ISO/OSI layer: 1 or 2; default: 2

When launched, the script performs a test or a continuous series of tests that generates data (in SW or using a generator in the design), sets datapaths, and measures throughput.
When using TX DMA, the scripts uses the ``ndp-generate`` tool to generate and send packets via DMA into the FPGA FW.
Other source of data can be one of the HW packet generators inside the GLS module (see :ref:`GLS module documentation <gls_debug>`).
When using RX DMA, the script uses the ``ndp-read`` tool to accept packets from the FPGA.
Else packets are dropped in the RX DMA module, which can be observed using the ``nfb-dma`` tool.
The variations of tests are set by the `-m`, `--mode` parameter (the only required one).
One test run in the selected mode consists of multiple partial tests for different lengths of generated frames, defined by the `-s`, `--frame_size` parameter that expects three values in bytes like so: `min max step`.

Some tests require an available DMA controller; test mode `eth_gen` can be used for NDK firmware without a DMA controller.
More about DMA controllers in the NDK can be found in the :ref:`DMA module documentation <ndk_dma>`.

Using the `eth_gen` test as an example, the :ref:`HW generator <mfb_generator>` generates Ethernet frames of constant length and sends them to the output network interface at full speed.
In this test, packets pass through the application core so that the measured throughput corresponds with the throughput of the implemented application.
Automatically, the Ethernet PMA loopback is enabled in the FPGA so that the transmitted packets are received back into the FPGA (can be disabled using `-e`, `--ext_loop`).
The script measures the TX and RX data rates and continues to repeat the test for incrementing packet lengths until the maximum packet length is reached.
For each packet length, the test is repeated a number of times (set by the `-C`, `--test_cycles` parameter) and the results are averaged.
The data rates are calculated either at layer 1 or layer 2 (set by the `-r`, `--rate_layer` parameter).
The data rate calculation at layer 2 considers Ethernet frames from the destination MAC address to the end of the payload.
CRC is appended by the TX MAC module and removed by the RX MAC module, in the rest of the path inside the FPGA, CRC is absent, so frames are shorter by 4 Bytes.

.. Note::

    Some Ethernet Hard IPs (especially E-Tile and F-tile) may not receive data for transmission if they do not detect the Ethernet link.
    The test will not work in this case, so we recommend connecting an external QSFP loopback.

Below is an example of the script output after running test 1:

.. code-block:: text

    $ python3 gls_mod.py 1
    Test # 1 started...
    Selected DMA channels: 0,1,2,3,4,5,6,7

    Frame Size (with CRC):       64 [Bytes]
    ----------------------------------------
    DMA Stream: 0
    Stream Speed TX:            71.43 [Gbps]
    Stream Speed RX:            71.43 [Gbps]
    ----------------------------------------
    Total Speed TX:             71.43 [Gbps]
    Total Speed RX:             71.43 [Gbps]
    ========================================
    Frame Size (with CRC):       96 [Bytes]
    ----------------------------------------
    DMA Stream: 0
    Stream Speed TX:            79.31 [Gbps]
    Stream Speed RX:            79.31 [Gbps]
    ----------------------------------------
    Total Speed TX:             79.31 [Gbps]
    Total Speed RX:             79.31 [Gbps]
    ========================================
    Frame Size (with CRC):      128 [Bytes]
    ----------------------------------------
    DMA Stream: 0
    Stream Speed TX:            83.78 [Gbps]
    Stream Speed RX:            83.78 [Gbps]
    ----------------------------------------
    Total Speed TX:             83.78 [Gbps]
    Total Speed RX:             83.78 [Gbps]

Perhaps the most confusing can be the selection of channels for transmission and reception.
When transferring data through the DMA (i.e., using ndp-generate for transmission to TX DMA and using GLS Generator for transmission to RX DMA, or using TX DMA -> RX DMA loopback), the DMA channels are utilized as is set by the user.
However, when traffic passes through the Network Module (i.e., through the PMA or external loopback), the conversion between DMA-to-Ethernet and Ethernet-to-DMA channels, at least in the ndk-app-minimal design, causes channel mixing according to the configured distribution.
In the default configuration, do not expect packets to arrive on the same DMA channels on which they were transmitted.

The main reason to use  the channels parameter is in the case of a single GLS module in the design (= a single DMA stream) on a NIC with multiple Ethernet ports.
This way, it is possible to select one of/both Ethernet ports to be used in the test (considering the ndk-app-minimal design) as the bottom half of channels forwards traffic to the first Ethernet port, the top half to the second Ethernet port.

End of test
***********

A single run of the script takes a while and can be terminated using Ctrl+C (once).
Partial test is finished before exiting, which causes a slight delay.
When `-r`, `--repeat` option is used, the script continues to run tests until interrupted using Ctrl+C (once).
