.. _ndk_intel_pcie_mod:

PCIe module
^^^^^^^^^^^

The PCIe module contains components handling all PCIe communication.
The module is divided into two parts: The first part (PCIe core) depends on the FPGA used and contains an installation of PCIe Hard IP, configuration logic and :ref:`DeviceTree <ndk_devtree>` ROM (it contains a description of the firmware and can be read as a PCIe register).
The second part (PCIe CTRL) contains the Connection Block, which converts the Avalon-ST bus to the MFB and also ensures the connection of the PTC and MTC modules to the PCIe Hard IP.
The :ref:`PTC module <ptc>` acts as an abstraction layer for translating DMA transactions to PCIe transactions.
The :ref:`MTC module <mtc>` acts as a Master point on the :ref:`MI bus <mi_bus>`, which translate requests from the PCIe bus to the MI bus and handles their execution.
The PCIe module also includes the clock domains crossing on the MI bus.

.. image:: img/pcie_module_arch.svg
    :align: center
    :width: 100 %

**Supported PCIe Hard IP**

- R-Tile on Intel Agilex FPGA
- P-Tile on Intel Stratix 10 or Agilex FPGA

**References**

- `Intel R-Tile AVST Hard IP for PCI Express User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/ug/ug20316.pdf>`_
- `Intel P-Tile AVST Hard IP for PCI Express User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/ug/ug_ptile_pcie_avst.pdf>`_
- :ref:`PTC module documentation <ptc>`
- :ref:`MTC module documentation <mtc>`
- :ref:`MI bus specification <mi_bus>`
- :ref:`MFB bus specification <mfb_bus>`
- :ref:`MVB bus specification <mvb_bus>`
