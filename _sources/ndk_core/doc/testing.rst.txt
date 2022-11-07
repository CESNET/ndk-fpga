.. _ndk_testing:

NDK testing
-----------

This chapter describes how the NDK firmware and its HDL components can be tested:

- Test R/W access to scratch registers in the NDK firmware (:ref:`see below <ndk_testing_mi>`).
- Simple HW throughput tests can be executed using the :ref:`Gen Loop Switch (GLS) debug module <gls_debug>` (:ref:`see below <ndk_testing_gls>`).
- HDL components are tested by :ref:`verification, mainly using the UVM <uvm_ver>`.
- There is also a :ref:`simulation of almost the entire firmware using cocotb <cocotb_sim>` (however, it is not yet publicly available).

.. _ndk_testing_mi:

Testing R/W access to the scratch registers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The NDK firmware implements 64 32-bit scratch registers for testing purposes. Like other parts of the firmware, they are accessible via the :ref:`MI bus <ndk_mi>`. This address space is (among other things) stored in the :ref:`DeviceTree <ndk_devtree>`. The `nfb-bus tool <https://cesnet.github.io/ndk-sw/tools/nfb-bus.html>`_ can be used for easy R/W access to any register in the firmware that is mapped to the MI bus. The following example shows how to:

- read the first scratch register (the offset is 0x0 in the byte format) in the MI TEST SPACE component (selected using the DeviceTree path),
- write a new value (0x42) to it, and
- read it again.

.. code-block:: bash

    $ nfb-bus -p /firmware/mi_bus0/mi_test_space 0x0
    00000000
    $ nfb-bus -p /firmware/mi_bus0/mi_test_space 0x0 0x42
    $ nfb-bus -p /firmware/mi_bus0/mi_test_space 0x0
    00000042

You can test R/W requests to the NDK firmware address space of these scratch registers however you want. Similarly, in the future, you can access the registers in your own application that you build on the NDK platform.

.. _ndk_testing_gls:

GLS module tutorial
^^^^^^^^^^^^^^^^^^^

The NDK firmware may include a GLS module that is instantiated in each DMA stream between the application core and the DMA controller. The GLS module is used for testing purposes and contains HW packet generators, speed meters, and datapath switches. Please refer to the :ref:`GLS module documentation <gls_debug>` for a more information.

The GLS module also comes with a Python script (``<NDK-APP-XXX_root_directory>/ndk/ofm/comp/mfb_tools/debug/gen_loop_switch/sw/gls_mod.py``) that can be used to quickly perform several basic tests (modes). For example, you can measure the throughput of the NDK firmware. A list of tests can be obtained by running this script without parameters:

.. code-block::

    $ python3 gls_mod.py 
    gls_mod.py mode [port_list]
    Example: gls_mod.py 1 "0,1"

    Supported modes:
    1: HW Gen --> TX ETH     ==> RX ETH --> Black Hole; (ext. ETH loopback required)
    2: HW Gen --> TX ETH     ==> RX ETH --> RX DMA;     (ext. ETH loopback required)
    3: TX DMA --> TX ETH     ==> RX ETH --> Black Hole; (ext. ETH loopback required)
    4: TX DMA --> TX ETH     ==> RX ETH --> RX DMA;     (ext. ETH loopback required)
    5: HW Gen --> RX DMA     ###
    6: TX DMA --> Black Hole ###
    7: TX DMA --> Black Hole ### RX DMA --> Black Hole;
    8: TX DMA --> RX DMA     ### (internal DMA loopback)

Some tests require an available DMA controller; others require an external QSFP loopback for Ethernet. Test 1 can be used for NDK firmware without a DMA controller. In this test, the :ref:`HW generator <mfb_generator>` sends Ethernet packets of constant length to the output network interface at full speed. The script measures the transmission data rate and continues to repeat the test for incrementing packet lengths until the maximum packet length is reached.

.. warning::

    Some Ethernet Hard IPs (especially E-Tile and F-tile) may not receive data for transmission if they do not detect the Ethernet link. The test will not work in this case, so we recommend connecting an external QSFP loopback.

If an external QSFP loopback is connected, the transmitted packets are received back into the FPGA, where the script measures the receiving speed. In this test, packets pass through the application core so that the measured throughput corresponds with the throughput of the implemented application. The throughput calculation considers L2 packets from the destination MAC address to the end of the payload. Below is an example of the script output after running test 1:

.. code-block::

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

Some cards have multiple Ethernet ports. In this case, it is possible to select the number of ports to test with the ``port_list`` parameter when running the script. Other settings can be manually modified inside the script, such as the range and step of packet lengths or enabling the measurement report.
