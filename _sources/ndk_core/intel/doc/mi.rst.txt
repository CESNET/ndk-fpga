.. _ndk_intel_mi:

MI bus interconnect
^^^^^^^^^^^^^^^^^^^

MI bus interconnection allows access to Control and Status Register (CSR).
Communication via :ref:`the MI bus <mi_bus>` is always initiated by the software via direct memory access to the PCIe device (FPGA card).
The software sends a read or write PCIe transaction, which is then processed by :ref:`the MTC module <mtc>` implemented in the FPGA.
The MTC module acts as a Master point on the MI bus, which translate requests from the PCIe bus to the MI bus and handles their execution.
See :ref:`MI bus specification <mi_bus>`.

**MI address space definition**

A total of 26b address range is available, which is divided between the individual parts of the design.

.. code-block::

    0x00000000-0x000000FF -- Test space (debug R/W registers)
    0x00000100-0x00000FFF -- Reserved space
    0x00001000-0x000010FF -- ADC sensor (FPGA temperature,...)
    0x00001100-0x00001FFF -- Reserved space
    0x00002000-0x000020FF -- FPGA (SDM) controller
    0x00002100-0x00003FFF -- Reserved space
    0x00004000-0x000040FF -- Timestamp unit
    0x00004100-0x00004FFF -- Reserved space
    0x00005000-0x00007FFF -- Debug Gen Loop modules
    0x00008000-0x0000BFFF -- Network module
    0x0000C000-0x0000FFFF -- Reserved space
    0x00010000-0x0001FFFF -- Memory controller (TODO)
    0x00020000-0x007FFFFF -- Reserved space
    0x00800000-0x00FFFFFF -- Ethernet physical layer
    0x01000000-0x013FFFFF -- DMA space
    0x01400000-0x01FFFFFF -- Reserved space
    0x02000000-0x03FFFFFF -- Application core

.. note::

    A module with an allocated address space can further divide its address space into its subcomponents.
    A description of the address space allocation should be included in DevTree.

.. warning::

    The address space description is still in draft and is subject to change!

**References**

- :ref:`MI bus specification <mi_bus>`
- :ref:`PCIe module documentation <ndk_intel_pcie_mod>`
- :ref:`MTC module documentation <mtc>`
