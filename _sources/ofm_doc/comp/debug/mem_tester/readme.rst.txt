.. _mem_tester:

DDR4 Memory Tester
------------------

Used acronyms:

- EMIF  ... External Memory InterFace
- AMM   ... Avalon Memory-Mapped
- FSM   ... Finite State Machine

This component is used to test external DDR4 memory.
It has to be connected to EMIF Hard IP which communicates with external DDR4 memory.

**References**

- `External Memory Interfaces Intel Stratix 10 FPGA IP User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-emi.pdf>`_
- `External Memory Interfaces Intel Agilex FPGA IP User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/agilex/ug-ag-emi.pdf>`_
- `Avalon Interface Specifications (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/manual/mnl_avalon_spec.pdf>`_

Internal Architecture
^^^^^^^^^^^^^^^^^^^^^

Architecture description:

- :ref:`MI bus <mi_bus>` logic is separated into another file (mem_tester_mi.vhd)

  - :ref:`MI_ASYNC <mi_async>` is used to cross between MI bus and Avalon clock domains
  - :ref:`MI_SPLITTER_PLUS_GEN <mi_splitter_plus_gen>` divides MI bus for mem_tester, AMM_GEN and AMM_PROBE components

- :ref:`AMM_GEN <mem_tester_amm_gen>` can be used to manually access the external memory
- :ref:`AMM_PROBE <mem_tester_amm_probe>` handles all the measurements (data flow, latency, r/w AMM word count)
- :ref:`LFSR_SIMPLE_RANDOM_GEN <lfsr_simple_random_gen>` components generate random data and addresses for testing external memory
- AMM interface from EMIF IP is connected to:
  
  - Internal logic during memory test 
  - :ref:`AMM_GEN <mem_tester_amm_gen>` during the manual access
  
- The whole component is then controlled by FSM

.. image:: doc/memory_tester.svg
      :align: center
      :width: 60 %

One Avalon MM transaction (burst) is made by sending/receiving ``burst_cnt`` data words.

Test of the external memory is divided into three steps:

- Writing pseudo-random data to all addresses of the memory
- Resetting pseudo-random generator (so it will generate the same data as before)
- Reading data back from the memory and comparing them with generated pseudo-random data
  
  - If the data do not match, the error counter will increment by 1

Pseudo-random data are selected to maximalize changes in data bits, and therefore 
revealing possible problems with memory or its connection.

.. toctree::
  :maxdepth: 2
  :hidden:

  amm_gen/readme
  amm_probe/readme

MI Bus Control
^^^^^^^^^^^^^^

**MI Address Space Definition**

.. code-block::

    0x0000 -- ctrl in
              0. bit -- reset
              1. bit -- run test
              2. bit -- connect mi2amm to AMM bus
              3. bit -- random addressing enable
    0x0004 -- ctrl out
              0. bit -- test done
              1. bit -- test successful
              2. bit -- ECC error occured
              3. bit -- calibration succes
              4. bit -- calibration fail
              7. bit -- write ticks overflow occurred
              8. bit -- read ticks overflow occurred
    0x0008 -- err cnt
    0x000C -- write ticks
    0x0010 -- read ticks
    0x0040 -- AMM_GEN   base address
    0x0080 -- AMM_PROBE base address


Mem_tester component reacts only to rising_edge change in bits inside ``ctrl in`` register, except:

- ``reset`` bit

It's recommended to clear those bits after usage, so they can be then set again.

**Usage**

Reset sequence:

- Set ``reset`` bit to ``1`` and then to ``0``
- Wait for either ``calibration successful`` bit or ``calibration fail`` bit

Run test:

- To run the test set ``run test`` bit to ``1``
- After the test is finished ``test done`` bit will be set to ``1`` and the result will be available in ``test successful`` bit
- Total number of clock cycles (ticks) needed to perform writing during the test is stored in ``write ticks`` register
  
  - Number of ticks needed for reading is stored in ``read ticks`` register
  - If read/write time was too long and ticks counters overflowed, it's signalized by ``write/read ticks overflow occurred`` bits

C Program Control
^^^^^^^^^^^^^^^^^

**Argument Definition**

- ``-d path``
  - Path to the device
- ``-c comp``
  - Compatibile of the mem_tester component [default: ``netcope,mem_tester``]
- ``-t type``              
  - Run test [type = all / seq / rand]
- ``-b``              
  - Boot again (reset)
- ``-p``              
  - Print registers
- ``-a addr``              
  - Address for manual r/w from/to the memory
- ``-m burst_id data``
  - Content of a AMM word (512b hexa) inside manual r/w buffer at position burst_id
- ``-r``              
  - Manual read
- ``-w``              
  - Manual write
- ``-h``              
  - Print help

**Usage**

Manual write to the external memory:

- First, fill the manual r/w buffer using ``-m burst_id data`` command:
  
  - ``burst_id`` parameter (in range: ``0 to BURST_CNT - 1``) selects which AMM word will be set
  - ``data`` parameter is a new AMM word (512b number in hexa)

- Set address at which should be data written using ``-a addr`` argument
- After running the program with ``-w`` flag, data will be saved to external memory

Manual read from the external memory:

- Set address from which should be data read using ``-a addr`` argument
- Run program with ``-r`` flag
- Wait until ``buff vld`` bit is set (use ``-p`` flag to print the current state of all bits and registers)
- Data will be then inside manual r/w buffer, which can be printed using ``-p`` flag
