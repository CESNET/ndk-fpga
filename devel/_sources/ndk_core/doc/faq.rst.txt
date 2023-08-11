.. _ndk_faq:

Frequently Asked Questions
==========================

What is a Network Development Kit (NDK)?
****************************************

The NDK is a generic FPGA framework for easy development of your own high-speed network FPGA application. `CESNET (an association of universities of the Czech Republic and the Czech Academy of Sciences) <https://www.cesnet.cz/cesnet/?lang=en>`_ develops and uses NDK primarily to implement own FPGA probes for monitoring CESNET high-speed backbone networks.

What SW do I need to build the NDK firmware?
********************************************

Intel Quartus Prime Pro tool is required to build FW with target FPGA from Intel. Xilinx Vivado tool is needed to build FW with target FPGA from Xilinx (AMD). You also need to have the corresponding licenses for these tools. The specific required versions of these tools are listed for each NDK application in the main README.md file.

What FPGA chips and cards does NDK support?
*******************************************

The NDK supports FPGA chips from both major manufacturers Intel and Xilinx (AMD). Specifically, these are Intel Agilex, Stratix 10 and Xilinx UltraScale+ FPGA chips. A list of specific supported FPGA cards is available for each NDK application in the main README.md file.

What communication interfaces can a NDK applications have available?
********************************************************************

A NDK application can use the interface for communication with external memories, for network communication (Ethernet), for software configuration (write and read 32b words) and for high-speed data transfers between the FPGA and the host memory (DMA).

What Ethernet standards does NDK support?
*****************************************

The specific support of Ethernet standards is always dependent on the target FPGA card or on the Ethernet IP used. NDK currently supports Intel E-Tile, F-Tile or Xilinx CMAC Ethernet IP. All listed IPs support the 100GBASE standard; E-Tile, F-Tile also handle 10GBASE and 25GBASE; and F-Tile then supports even more Ethernet standards.

Does NDK implement ISO/OSI protocol support?
********************************************

No, the user application in the NDK must work on the line layer (L2), i.e. with Ethernet frames without CRC (it is removed/added in the Ethernet IP). If necessary, support for ISO/OSI protocols must be implemented within the user application.

Does NDK support Jumbo packets?
*******************************

Yes, the NDK firmware supports packets up to 16383 B by default, which is the maximum possible value. However, the RX MAC by default discards received Ethernet frames larger than 1522 B (including CRC), but this limit can be changed dynamically through the SW tool (nfb-eth).

Is there also an open-source DMA controller available?
******************************************************

Not currently, but a low-latency DMA controller (DMA Calypte) is currently under development, which will be available as an open-source component of the NDK.

What clock frequencies are available for the user application?
**************************************************************

The user application in the NDK has available four clock signals from the same source with frequencies: 100, 200, 300 and 400 MHz. A 100MHz clock is typically used for the configuration interface and the default is 200MHz for the data path. Using a slower clock may degrade the overall throughput of the NDK.

Is there a SW stack also available for the NDK?
***********************************************

Yes, a Linux driver, a library with a simple API for developing your own SW application and a set of useful tools are available in a `separate repository <https://github.com/CESNET/ndk-sw>`_.

What is the difference between NDK and NetFPGA?
***********************************************

NetFPGA is a general framework for developing your own FPGA application same as the NDK. Unfortunately NetFPGA only supports Xilinx UltraScale+ FPGA chips and does not support Ethernet and data rates higher than 100 Gbps.

What is the difference between NDK and Corundum?
************************************************

Rather, Corundum is also trying to create a general FPGA network, but it also enables the expansion of its own RTL application. Corundum also supports various FPGA cards with chips from both Xilinx and Intel. Unfortunately it does not support Ethernet and data transfer rates higher than 100 Gbps.

What is the difference between NDK and OpenNIC?
***********************************************

OpenNIC is a general framework for developing your own FPGA application same as the NDK. Unfortunately OpenNIC only supports Xilinx UltraScale+ FPGA chips and does not support Ethernet and data transfer speeds higher than 100 Gbps.
