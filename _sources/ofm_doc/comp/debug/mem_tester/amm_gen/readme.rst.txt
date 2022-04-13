.. _mem_tester_amm_gen:

AMM_GEN
-------

This component is used to manually read or write to the external memory from the MI bus via the AMM bus.
It has to be connected to EMIF Hard IP which then communicates directly with external DDR4 memory.

Internal Architecture
^^^^^^^^^^^^^^^^^^^^^

AMM data bus width is significantly larger than MI data bus width and
all data words in the burst have to be sent/received in one continuous request.
Therefore there is a buffer that can be first filled with MI bus transactions and then sent to EMIF. 
When manual read from memory is requested, the buffer is first automatically filled and then can be read
by MI bus registers.

- DP_BRAM buffer keeps ``BURST_CNT`` AMM words

  - Data are r/w from/to the buffer either by AMM interface or by internal logic
  - Therefore dual-port memory is selected
  
- One of ``internal logic`` tasks is to cross between ``MI_DATA_WIDTH`` words and ``AMM_DATA_WIDTH`` words
  
  - It keeps currently selected AMM word from the buffer and when ``data`` register is updated from the MI bus
    corresponding slice in this ``AMM_DATA_WIDTH`` word is replaced with a new data (``MI_DATA_WIDTH``)
  - This edited word is then saved to the buffer
  
- EDGE_DETECT is used to detect just rising edge of bits inside ``ctrl`` register
- The whole component is then controlled by FSM

.. image:: doc/AMM_GEN.svg
      :align: center
      :width: 90 %

MI Bus Control
^^^^^^^^^^^^^^

**MI Address Space Definition**

.. code-block::

    BASE + 0x00 -- ctrl
                  0. bit -- memory write
                  1. bit -- memory read
                  2. bit -- buff valid
                  3. bit -- amm ready
    BASE + 0x04 -- address
    BASE + 0x08 -- data

**Usage**

Manual write to the external memory:

- Filling buffer:

  - First set ``address`` register to select slice in the buffer that will be edited 
  
    - Slice = MI_DATA_WIDTH word inside AMM_DATA_WIDTH word
    - Address should be in range ``0 to SLICES_CNT - 1``
    - ``SLICES_CNT = (AMM_DATA_WIDTH / MI_DATA_WIDTH) * BURST_CNT``
    - Slice at address 0 is LSB of the first AMM word
  
  - Then set ``data`` registers with the data for selected slice
  - Repeat these steps for all slices of the burst

- Set ``manual address`` register to address for writing (indexing by AMM words)
- Data can be then saved from buffer to external memory by setting ``memory write`` bit to ``1``

Manual read from the external memory:

- Set ``manual address`` register to required address (indexing by AMM words)
- To load data from external memory into the buffer set ``memory read`` bit to ``1``
- Wait until ``buff valid`` bit is asserted to ``1``
- Set ``address`` register to value in range ``0 to SLICES_CNT - 1``
- Selected slice (MI word) can be then accessed in ``data`` registers
