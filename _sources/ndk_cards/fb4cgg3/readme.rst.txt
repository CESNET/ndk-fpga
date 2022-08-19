.. _card_fb4cgg3:

FB4CGG3/FB2CGG3 cards
---------------------

FB4CGG3/FB2CGG3 cards by Silicom are supported in the NDK.

Build instructions
^^^^^^^^^^^^^^^^^^

- Go to ``build/fb4cgg3/`` folder in application repository.
- Check or modify ``user_const.tcl`` file, where you can change the firmware configuration.
- Run firmware build in Vivado by ``make`` command.
    - Use ``make 100g2`` command for firmware with 2x100GbE for FB2CGG3 card (default).
    - Use ``make 100g4`` command for firmware with 4x100GbE for FB4CGG3 card.
- After the build is complete, you will find bitstream in the same folder.

.. note::

    To build firmware, you must have Xilinx Vivado installed, including a valid license.

Boot instructions
^^^^^^^^^^^^^^^^^^

- To boot design on specific card you have to follow these steps:
    - Copy .nfw file into current directory 
    - Boot design by using ``nfb-boot -f 0`` command in directory where .nfw file is located.
        - ``nfb-boot -f 0 fb2cgg3-minimal-100g2.nfw`` command for 2x100GbE firmware
        - ``nfb-boot -f 0 fb4cgg3-minimal-100g4.nfw`` command for 4x100GbE firmware
- To confirm that design is booted correctly use ``nfb-info`` command

.. note::

    To see boot options use command ``nfb-boot -h``.

Ethernet Interface
^^^^^^^^^^^^^^^^^^

This card has four (FB4CGG3) or two (FB2CGG3) QSFP ports. Each port is connected to the FPGA via 4 high-speed serial lines supporting up to 25 Gbps. Each of these ports is connected to CMAC core with speed of ``1x100GE``. The architecture of network module :ref:`is described here <ndk_intel_net_mod>`.


PCIe Interface
^^^^^^^^^^^^^^^^^^

This card has single PCIe Gen3 x16 edge connector. The throughput available to the user is approximately 100 Gbps and is depend on DMA solution. The architecture of the PCIe Module :ref:`is described here <ndk_intel_pcie_mod>`.
