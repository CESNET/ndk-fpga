Documentation of Minimal NDK Application 
****************************************

**Welcome to documentation of Minimal NDK Application!**

The Network Development Kit (NDK) allows users to quickly and easily develop new network appliances based on FPGA acceleration cards. The NDK is optimized for high throughput and scalable to support 10, 100 and 400 Gigabit Ethernet.

.. image:: img/liberouter_logo.svg
    :align: center
    :width: 50 %
 
The Minimal application serves as a simple example of how to build an FPGA application using the Network Development Kit (NDK). It can also be used as a starting point for building your own application. The Minimal application does not process network packets in any way, it can only receive and send them. If the DMA module IP is enabled, the network packets are forwarded to the computer memory.

.. warning::

    The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback. `You can get NDK including DMA Module IP and professional support through our partner BrnoLogic <https://support.brnologic.com/>`_.

.. note::

    To build FPGA firmware, you must have Intel Quartus Prime Pro 22.2 or Xilinx Vivado 2019.1 (depending on the target card) installed, including a valid license.

.. toctree::
    :maxdepth: 2
    :caption: Application:
    :hidden:

    app-minimal

.. toctree::
    :maxdepth: 2
    :caption: Network Development Kit:
    :hidden:

    ndk_core/doc/how_to_start
    ndk_core/doc/terminology
    ndk_core/intel/readme
    ndk_core/doc/configuration
    ndk_core/doc/testing
    ofm_doc/build/readme
    ndk_core/doc/devtree

.. toctree::
    :maxdepth: 2
    :caption: Supported cards:
    :hidden:

    ndk_cards/agi-fh400g/readme
    ndk_cards/dk-dev-1sdx-p/readme
    ndk_cards/dk-dev-agi027res/readme
    ndk_cards/fb4cgg3/readme
    ndk_cards/fb2cghh/readme
    ndk_cards/ia-420f/readme
    ndk_cards/nfb-200g2ql/readme

.. toctree::
    :maxdepth: 2
    :caption: VHDL components:
    :hidden:

    ofm_doc/base
    ofm_doc/ctrls
    ofm_doc/mi
    ofm_doc/mfb
    ofm_doc/mvb
    ofm_doc/nic
    pcie
    ofm_doc/debug
    ofm_doc/ver
