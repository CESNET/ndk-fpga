FIFO components
===============

.. _asfifo_modules:

Dual clock (asynchronous) FIFOs
-------------------------------

**ASFIFO** - Behavioral dual clock FIFO implementation based on LUTMEMs and optimized for Xilinx only. Include status signal. ``OBSOLETE, use ASFIFOX!``

**ASFIFO_BRAM** - Behavioral dual clock FIFO implementation based on BRAMs and optimized for Xilinx only. Include status signal. ``OBSOLETE, use ASFIFOX!``

**ASFIFO_BRAM_BLOCK** - Similar to ASFIFO_BRAM but with extra signal to mark end of input data block, output remains in empty state until such mark is received. Located in the same folder as ASFIFO_BRAM.

**ASFIFO_BRAM_RELEASE** - Similar to ASFIFO_BRAM but contains two extra signals,
one (MARK) is used for detecting end of input data blocks and second (DRELEASE) says that there is possibility of releasing the last data block.
Located in the same folder as ASFIFO_BRAM.

**ASFIFO_BRAM_DATAMUX** - The set of dual clock FIFO implementations with doubled data width on the input or output, based on ASFIFO_BRAM_XILINX (Xilinx only).

**ASFIFO_BRAM_XILINX** - Structural implementation of dual clock FIFO based on Xilinx specific BRAM FIFO primitives (no extra logic). Include almost full and almost empty signal.

**ASFIFOX** - Universal dual clock FIFO for Xilinx and Intel FPGAs. It support various memory implementation: LUTMEMs, BRAMs. Include almost full, almost empty and status signal.
Detailed :ref:`documentation can be found here<asfifox>`.

.. toctree::
   :maxdepth: 1
   :hidden:

   comp/base/fifo/asfifox/readme

.. _fifo_modules:

Single clock FIFOs
------------------

**FIFO** - Behavioral FIFO implementation based on LUTMEMs and optimized for Xilinx only. Include status signal. ``OBSOLETE, use FIFOX!``

**FIFO_BRAM** - Behavioral FIFO implementation based on BRAMs and optimized for Xilinx only. Include status signal. ``OBSOLETE, use FIFOX!``

**FIFO_BRAM_XILINX** - Structural implementation of FIFO based on Xilinx specific BRAM FIFO primitives (no extra logic). Include almost full and almost empty signal.

**FIFO_N1** - Behavioral implementation of FIFO with multiple write ports, it based on LUTMEMs and optimized for Xilinx only. ``OBSOLETE, use FIFOX_MULTI!``

**FIFOX** - Universal FIFO for Xilinx and Intel FPGAs. It support various memory implementation: LUTMEMs, BRAMs, URAMs (Xilinx only) and shift-registers in LUT slices (effective on Xilinx only).
Include almost full, almost empty and status signal. Possible automatic selection of a suitable memory implementation. Detailed :ref:`documentation can be found here<fifox>`.

**FIFOX_MULTI** - Universal FIFO based on FIFOX, which allows multiple write and read requests in each cycle. Detailed :ref:`documentation can be found here<fifox_multi>`.

**MULTI_FIFO** - Behavioral implementation of FIFO for Xilinx and Intel FPGAs with multiple independent channels. It support various memory implementation: LUTMEMs, BRAMs, URAMs (Xilinx only).
The memory type is selected automatically.

**SH_FIFO** - Behavioral FIFO implementation based on shift-registers in LUT slices and optimized for Xilinx only. ``OBSOLETE, use FIFOX!``

.. toctree::
   :maxdepth: 1
   :hidden:

   comp/base/fifo/fifox/readme
   comp/base/fifo/fifox_multi/readme

References
----------

- `UG573 - UltraScale Architecture Memory Resources <https://www.xilinx.com/support/documentation/user_guides/ug573-ultrascale-memory-resources.pdf>`_
- `UG574 - UltraScale Architecture CLB User Guide <https://www.xilinx.com/support/documentation/user_guides/ug574-ultrascale-clb.pdf>`_
- `UG-S10MEMORY - Intel Stratix 10 Embedded Memory User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-memory.pdf>`_
- `UG-20208 - Intel Agilex Embedded Memory User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/agilex/ug-ag-memory.pdf>`_
