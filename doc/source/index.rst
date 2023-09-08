Documentation of Minimal NDK Application 
****************************************

**Welcome to documentation of Minimal NDK Application!**

The NDK-APP-Minimal is a reference application based on the Network Development Kit (NDK) for FPGAs. The NDK allows users to quickly and easily develop FPGA-accelerated network applications. The NDK is optimized for high throughput and scalability to support up to 400 Gigabit Ethernet.

.. image:: img/liberouter_logo.svg
    :align: center
    :width: 50 %

The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled (see the :ref:`DMA Module chapter <ndk_dma>`), then it forwards the network packets to and from the computer memory.

.. warning::

    The DMA Medusa IP is not part of the open-source NDK. `You can get the NDK, including the DMA Medusa IP and professional support, through our partner BrnoLogic. <https://support.brnologic.com/>`_

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

    ndk_cards/reflexces/agi-fh400g/readme
    ndk_cards/intel/dk-dev-1sdx-p/readme
    ndk_cards/intel/dk-dev-agi027res/readme
    ndk_cards/silicom/fb4cgg3/readme
    ndk_cards/silicom/fb2cghh/readme
    ndk_cards/silicom/n6010/readme
    ndk_cards/bittware/ia-420f/readme
    ndk_cards_private/nfb-200g2ql/readme

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
    ofm_doc/pcie
    ofm_doc/debug
    ofm_doc/ver
