Memory modules
==============

**CAM** - Ternary content addressable memory implemented in memory LUTs, optimized for Xilinx only. Also there is **light variant** implemented using register array, simpler but less effective.

**DP_BMEM** - Behavioral implementation of dual clock BRAM memory with two read/write port. ``OBSOLETE, use DP_BRAM or DP_BRAM_XILINX!``

**DP_BMEM_V7** - Structural implementation of dual clock BRAM memory based on Virtex 7 specific primitives with two read/write ports. ``OBSOLETE, use DP_BRAM or DP_BRAM_XILINX!``

**DP_BRAM** - Behavioral implementation of single clock BRAM memory with two read/write port. Optimized for Xilinx and Intel FPGAs.

**DP_BRAM_XILINX** - Structural implementation of dual clock BRAM memory based on Xilinx specific primitives with two read/write ports. Only for Xilinx FPGAs.

**DP_URAM_XILINX** - Structural implementation of single clock URAM memory based on Xilinx specific primitives with two read/write ports. Only for Xilinx UltraScale+ FPGAs.

**GEN_LUTRAM** - Generic implementation of LUT memory. Allows setting the number of read ports and read latency (from 0 clock cycles).
Optimized for Xilinx Virtex 7, UltraScale+ and Intel Arria 10, Stratix 10, Agilex.

**GEN_REG_ARRAY** - Generic behavioral implementation of register array. Allows setting the number of read and write ports and read latency (from 0 cycles).
Effective only for small data arrays.

**NP_LUTRAM** - Advance generic implementation of LUT memory. Allows setting the number of read ports and write ports.
The read latency is 0 clock cycles. Optimized for same FPGAs as GEN_LUTRAM.

**NP_LUTRAM_PRO** - An alternative version of NP_LUTRAM, which uses additional multiple frequency clock signal.
Ports are registered and the read latency is 2 clock cycles. Expert knowledge is required to use this component!

**SDP_BMEM** - Behavioral implementation of dual clock BRAM memory with one read port and one write port. Located in the same folder as DP_BMEM. ``OBSOLETE, use DP_BRAM or DP_BRAM_XILINX!``

**SDP_BMEM_V7** - Structural implementation of dual clock BRAM memory based on Virtex 7 specific primitives with one read port and one write port.
Located in the same folder as DP_BMEM_V7. ``OBSOLETE, use SDP_BRAM or SDP_BRAM_XILINX!``

**SDP_BRAM** - Structural implementation of dual clock BRAM memory based on Xilinx and Intel specific primitives (xpm_memory_sdpram, altera_syncram) with one read port and one write port.
It supports the byte enable feature!

**MP_BRAM** - Generic multiported single clock BRAM memory based on **SDP_BRAM**. Currently supports only 1 write port. Amount of read ports is not restricted. Also supports byte enable
feature.

**SDP_BRAM_BEHAV** - Another behavioral implementation of dual clock BRAM memory with one read port and one write port.
Located in the same folder as SDP_BRAM. ``OBSOLETE, use DP_BRAM or DP_BRAM_XILINX!``

**SDP_BRAM_XILINX** - Structural implementation of dual clock BRAM memory based on Xilinx specific primitives with one read port and one write port. Only for Xilinx FPGAs.

**SDP_MEMX** - Universal behavioral implementation of single clock memory with one read port and one write port.
Allows setting type of memory (LUT, BRAM, URAM) or automatic mode. Optimized for Xilinx and Intel FPGAs.

**SDP_URAM_XILINX** - Structural implementation of single clock URAM memory based on Xilinx specific primitives with one read port and one write port. Only for Xilinx UltraScale+ FPGAs.

**SP_BMEM** -  Old behavioral implementation of single clock BRAM memory with one read/write port. ``OBSOLETE, use SP_BRAM or SP_BRAM_XILINX!``

**SP_BRAM** - Behavioral implementation of single clock BRAM memory with one read/write port. Optimized for Xilinx and Intel FPGAs.

**SP_BRAM_XILINX** - Structural implementation of single clock BRAM memory based on Xilinx specific primitives with one read/write port. Only for Xilinx FPGAs.

**SP_URAM_XILINX** - Structural implementation of single clock URAM memory based on Xilinx specific primitives with one read/write port. Only for Xilinx UltraScale+ FPGAs.

.. toctree::
   :maxdepth: 1
   :hidden:
          
   comp/base/mem/np_lutram/readme
   comp/base/mem/sdp_bram/readme
   comp/base/mem/mp_bram/readme
..   comp/base/mem/<something>
             
References
----------

- `UG573 - UltraScale Architecture Memory Resources <https://www.xilinx.com/support/documentation/user_guides/ug573-ultrascale-memory-resources.pdf>`_
- `UG574 - UltraScale Architecture CLB User Guide <https://www.xilinx.com/support/documentation/user_guides/ug574-ultrascale-clb.pdf>`_
- `UG-S10MEMORY - Intel Stratix 10 Embedded Memory User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-memory.pdf>`_
- `UG-20208 - Intel Agilex Embedded Memory User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/agilex/ug-ag-memory.pdf>`_
