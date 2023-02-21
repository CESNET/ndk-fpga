.. _ndk_mi:

The MI bus interconnect
=======================

The NDK provides the `nfb-bus tool <https://cesnet.github.io/ndk-sw/tools/nfb-bus.html#nfb-bus>`_ and an `API for generating read/write memory requests <https://cesnet.github.io/ndk-sw/libnfb-quick-start-registers.html>`_. These requests are transferred via the :ref:`MI bus <mi_bus>` in the NDK firmware. This memory-oriented bus is wired throughout the NDK firmware and each part has an allocated address space. The components accessible over the MI bus and their specific address spaces are described in the NDK using a :ref:`DeviceTree <ndk_devtree>`. 

The MI bus interconnection allows easy access to implemented Control/Status Registers (CSR). Communication via the :ref:`MI bus <mi_bus>` is always initiated by the software via direct memory access to the PCIe device (FPGA card) memory space. The software sends a read or write PCIe transaction, which is then processed by the :ref:`MTC module <mtc>` implemented in the FPGA. The MTC module acts as a Master point on the MI bus. It translates requests from the PCIe bus to the MI bus and handles their execution.

.. WARNING::
    A read request to a non-existent/non-implemented memory space in the FPGA can deadlock the NDK firmware or the entire PCIe communication.

The main allocation of the MI address space
*******************************************

An address range of 26 bits is available for the whole NDK firmware. It is divided between the individual parts of the design. The main allocation of the MI address space must be identically described in the VHDL package ``<NDK-APP-XXX_root_directory>/ndk/core/intel/src/mi_addr_space_pkg.vhd`` and in the DeviceTree file of the NDK-CORE ``<NDK-APP-XXX_root_directory>/ndk/core/intel/src/DevTree.tcl``. This allocation can also be found below:

.. code-block::

    0x00000000-0x000000FF -- Test space (debug R/W registers)
    0x00000100-0x00000FFF -- Reserved space
    0x00001000-0x00001FFF -- SDM/SYSMON controller (FPGA temp, Intel ASx4 boot,...)
    0x00002000-0x00002FFF -- BOOT controller (generic flash access)
    0x00003000-0x00003FFF -- Ethernet PMD (QSFP controller)
    0x00004000-0x000040FF -- Timestamp unit
    0x00004100-0x00004FFF -- Reserved space
    0x00005000-0x00007FFF -- Debug GLS modules
    0x00008000-0x0000BFFF -- Ethernet MACs
    0x0000C000-0x0000FFFF -- Reserved space
    0x00010000-0x0001FFFF -- DRAFT: Memory controller
    0x00020000-0x007FFFFF -- Reserved space
    0x00800000-0x00FFFFFF -- Ethernet PCS/PMA
    0x01000000-0x013FFFFF -- DMA controller
    0x01400000-0x01FFFFFF -- DRAFT: MSIX controller
    0x02000000-0x03FFFFFF -- The Application

.. NOTE::
    A module with an allocated address space can further divide it among its subcomponents. A description of the address space allocation must be included in DevTree.
