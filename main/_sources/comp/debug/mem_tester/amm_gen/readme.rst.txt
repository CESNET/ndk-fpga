.. _amm_gen:

AMM_GEN
-------

This component is used to manually read or write to the external memory from the MI bus via the AMM bus.
It has to be connected to EMIF Hard IP.

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

  - It keeps currently selected AMM word from the buffer
  - This word can be edited from MI bus
  - Editing will automatically update buffer

- EDGE_DETECT is used to detect rising edge changes of bits inside ``ctrl`` register
- The whole component is then controlled by FSM

.. image:: doc/AMM_GEN.svg
      :align: center
      :width: 90 %

.. note::
  Slice = MI_DATA_WIDTH word inside AMM_DATA_WIDTH word

MI Bus Control
^^^^^^^^^^^^^^

**MI Address Space Definition**

.. code-block::

    BASE + 0x00 -- ctrl
                  1. bit -- memory write
                  2. bit -- memory read
                  3. bit -- buff valid
                  4. bit -- amm ready
    BASE + 0x04 -- address / burst
    BASE + 0x08 -- slice (MI word slice inside AMM word)
    BASE + 0x0C -- data
    BASE + 0x10 -- burst count

**Usage**

Manual write to the external memory:

- Filling buffer:

  - First set ``address / burst`` register to select AMM word in the buffer that will be edited
  - Then set the ``slice`` register to select slice inside selected AMM word
  - Then set ``data`` registers with the data for selected slice
  - Repeat these steps for all slices of the burst

- Set ``address / burst`` register to address for writing (indexing by AMM words)
- Data can be then saved from buffer to external memory by setting ``memory write`` bit to ``1``

Manual read from the external memory:

- Set ``manual address`` register to required address (indexing by AMM words)
- To load data from external memory into the buffer set ``memory read`` bit to ``1``
- Wait until ``buff valid`` bit is asserted to ``1``
- Repeat steps from 'Filling buffer' to read received words
