.. _ndk_pcie_mod:
.. _ndk_intel_pcie_mod:

The PCIe module
===============

The PCIe module handles all PCIe communication. Its task is to forward/transform PCIe transactions for the DMA controller and the :ref:`MI bus <mi_bus>`. The architecture of the PCIe module is divided into two main parts: PCIE_CORE and PCIE_CTRL. Its diagram is shown below.

.. image:: img/pcie_module_arch.drawio.svg
    :align: center
    :width: 100 %

.. NOTE::
    The PCIe module can support more than one PCIe endpoint. In this case, the individual parts of the PCIe module are appropriately duplicated for each PCIe endpoint. There is also bifurcation support for some PCIe HARD IPs.

The PCIe Core (PCIE_CORE)
*************************

The PCIe Core varies according to the PCIe Hard IP or FPGA used. The PCIe Core contains the instance(s) of the used PCIe Hard IP, an adapter for converting the AXI/Avalon-ST buses to the :ref:`MFB buses <mfb_bus>`, the Vendor-Specific Extension Capability (VSEC) registers (implemented in the :ref:`PCI_EXT_CAP module <pci_ext_cap>`) containing mainly the :ref:`DeviceTree <ndk_devtree>` firmware description and additional configuration logic. Thus, the main purpose of the PCIe Core is to unify the buses and provide the necessary information about the active PCIe link.

Supported PCIe Hard IP
----------------------

A list of the supported PCIe Hard IPs is below. You can select the target architecture by setting the NDK parameter ``PCIE_MOD_ARCH``. According to this parameter, the correct PCIE_CORE module variant is used and the VHDL generic ``PCIE_ENDPOINT_TYPE`` is set appropriately.

- ``R_TILE`` - `R-Tile Avalon Streaming Intel FPGA IP for PCI Express <https://www.intel.com/content/www/us/en/docs/programmable/683501/>`_
- ``P_TILE`` - `P-Tile Avalon Streaming Intel FPGA IP for PCI Express <https://www.intel.com/content/www/us/en/docs/programmable/683059/>`_
- ``USP`` - `Xilinx UltraScale+ Device Integrated Block for PCI Express <https://docs.xilinx.com/r/en-US/pg213-pcie4-ultrascale-plus>`_

The PCIe Control unit (PCIE_CTRL)
*********************************

The PCIe Control unit always includes the :ref:`MI Transaction Controller (MTC) <mtc>`, which transforms the associated PCIe memory transactions into read or write requests on the MI bus. In the case of a read request, the MI response is also transformed back into a PCIe completition transaction and sent back to the host PC. PCIe transactions from the BAR0 address space are allocated to the MTC module. If the NDK uses a DMA controller that requires its own BAR, the PCIe transactions from the DMA-BAR address space (BAR2) are routed directly to the DMA module. This functionality must be enabled via the ``DMA_BAR_ENABLE`` parameter.

.. NOTE::
    We assume that 64-bit PCIe BARs are used, meaning that half of them are available at most (BAR0, BAR2, and BAR4). You can find more information in the PCIe specification.

By default, this unit also contains the :ref:`PTC module <ptc>`, which transforms memory requests (in a simplified format) coming from the DMA into the desired PCIe format and vice versa. The PTC module also implements a completion buffer and handles the allocation of the PCIe TAGs, etc. The PTC can be disabled using the ``PTC_DISABLE`` parameter, in which case the DMA requests (in the PCIe transaction format) are directly forwarded to the PCIe Hard IP and vice versa.

The PCIe module entity
**********************

.. vhdl:autoentity:: PCIE
