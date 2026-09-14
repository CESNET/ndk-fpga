.. _hbm_tester:

HBM Tester
----------

The ``HBM_TESTER`` component validates HBM (High Bandwidth Memory) throughput, latency and
data integrity. It stress-tests memory controllers and physical layers using both linear
and pseudorandom access patterns.

One tester is instantiated per physical HBM module, each in the clock and reset domain of
that module. The MI bus is bridged into the HBM clock domain by the internal ``MI_ASYNC``
component, so the tester can be controlled from the application clock domain.

Hardware Configuration
^^^^^^^^^^^^^^^^^^^^^^

* **Clock and Reset**

  * One HBM module has a single frequency and reset domain.
  * If the design has several HBM modules, instantiate a dedicated tester for each.

* **PORT_ADDR_HBIT** -- capacity (addressing range) of one port.

  * ``28`` for **256 MB**, ``29`` for **512 MB**, ``30`` for **1 GB**.

* **BASE_ADDR_OFFSET** -- size of one port in bytes, that is the step between the base
  addresses of two neighbouring ports. It must be a multiple of ``2**PORT_ADDR_HBIT``.
  The base address of a port is ``PORT_ID * BASE_ADDR_OFFSET``.

  * Use ``0`` when every port has its own address space, for example a NoC attached HBM.
  * For a 256 MB port packed into one map, use ``0x10000000``.

* **CNT_WIDTH** -- width of the test duration counter. The maximum duration is
  ``2**CNT_WIDTH`` clock cycles.

* **USE_AXI_ID** -- located in the ``HBM_TESTER_PORT`` module, the default is **False**.

  * **True**: generates unique AXI IDs for transactions. The memory (or its IP) then has
    to contain a reorder buffer, otherwise the responses may come back in a different
    order than the tester expects and the data integrity test reports false errors.
  * **False**: every transaction uses the same AXI ID, so AXI4 guarantees the order of
    responses within a single channel. AXI does not guarantee ordering between the write
    and read channels, see `Read after Write`_. Required if the system lacks a reorder
    buffer, which is the case for the NoC attached HBM on ThunderFjord (fb2cdg1).

Principle of Operation
^^^^^^^^^^^^^^^^^^^^^^

The ``HBM_TESTER_GEN`` module acts as a traffic generator and data integrity checker.

Address Generation
""""""""""""""""""

* **Sequential mode**: addresses increment linearly. The stride follows the burst length
  (BL4 or BL8) so that the generated traffic stays contiguous.
* **Pseudorandom mode**: a Linear Feedback Shift Register (LFSR) generates the addresses.
  Useful for worst-case latency, because it stops the HBM controller from consistently
  hitting open rows.

Data Generation and Integrity
"""""""""""""""""""""""""""""

* **Write path**: controlled by ``CS_GEN_WR_DEAD``. With ``0`` the word holds an
  incrementing counter in the first 8 bits and zeros in the rest. With ``1`` the whole
  word is the constant ``0xDEADCAFE`` and no counter is written.
* **Read path and verification**: the tester maintains an internal expected counter and
  compares it with the incoming ``RD_DATA(7 downto 0)``.
* **Statistics**: ``STAT_DATA_OK_INC`` pulses when the read data matches the expected
  counter, ``STAT_DATA_ERR_INC`` pulses on a mismatch.

.. note::
   Valid checking requires a strict "write then read" sequence.

Read after Write
""""""""""""""""

The AXI write and read channels are not ordered against each other. A read issued right
after a write to the same address may therefore be served first and return the old data,
which is what the ``coherency`` test looks for. The effect grows with the latency of the
memory path; on a NoC attached HBM the read wins often.

To keep this from firing on its own traffic, the generator only enables the read address
once the write response of the previous burst has arrived (``s_wr_rsp_pending`` in
``HBM_TESTER_GEN``). This applies to the R/W switching mode only and costs the full write
response latency between each write and its read, so that mode is not a bandwidth
measurement. Config bit ``[7]`` (``-w`` on the command line) turns the wait off, which
lets the test measure how often a read overtakes its write on a given memory path.

Traffic Control
"""""""""""""""

* **Write-only / Read-only**: continuous streams of a single transaction type.
* **R/W switching**: with ``CS_GEN_RW_SWITCH`` enabled the module toggles between writing
  a burst and reading an address, simulating bidirectional traffic.
* **Burst support**: **BL8** (64B access via two 256b words) and **BL4** (32B access).

.. warning::
   The burst is counted in bus words, so these sizes only hold on a 256b bus. On a 512b
   bus the same encoding issues 128B and 64B, and a real 32B access cannot be generated
   at all.

Component port and generics description
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: HBM_TESTER
   :noautogenerics:

Control Software
^^^^^^^^^^^^^^^^

The ``hbm_tester.py`` script in the ``sw`` directory controls the hardware.

.. warning::
   **The script is not self-configuring and has to be told the geometry of your build.**
   It does not read the geometry of the tester from the firmware or from the Device Tree,
   it assumes 32 ports per tester instance, a 256b data bus and a 450 MHz ``HBM_CLK``.
   When these defaults do not match the design, pass the correct values with ``-P``,
   ``-W`` and ``-F``, otherwise the script reports wrong numbers without any warning, or
   accesses the registers of ports that do not exist.

One ``hbm_tester`` object is created per Device Tree node, that is per HBM module, and the
values given on the command line are used for all of them. A design whose modules do not
have the same geometry is not supported by the script.

Tests
"""""

.. list-table::
   :header-rows: 1
   :widths: 20 80

   * - Test
     - What it does
   * - ``speed``
     - Writes and reads continuously and reports the throughput of each port.
   * - ``latency``
     - Same traffic, but reports the average read and write latency. Use ``-r`` for the
       worst case, it stops the controller from hitting open rows.
   * - ``integrity``
     - Writes the counter to all addresses, then reads them back and checks. Answers
       "does what I wrote come back?".
   * - ``coherency``
     - Fills the memory with ``0xDEADCAFE`` first, then writes the counter to an address
       and reads that same address straight back, alternating. The read has to return the
       counter, a returned ``0xFE`` means it overtook its own write. Answers "does a read
       right after a write see the new data?".

Command Line Arguments
""""""""""""""""""""""

.. list-table::
   :header-rows: 1
   :widths: 25 75

   * - Argument
     - Description
   * - ``-i, --index``
     - Index of the HBM tester (e.g. ``0``, ``1``), or ``all`` to run on all modules.
   * - ``-d, --device``
     - Device index (default: ``0`` for ``/dev/nfb0``).
   * - ``-t, --test``
     - Type of test: ``speed``, ``latency``, ``integrity`` or ``coherency``.
   * - ``-r, --random``
     - Enable random addressing (for latency or speed tests).
   * - ``-w, --no-wait``
     - Do not wait for the write response before reading the same address (coherency
       test).
   * - ``-p, --ports``
     - Number of active ports/channels (default: all).
   * - ``-P, --tester-ports``
     - Number of ports of **one** tester instance, that is ``HBM_PORTS / HBM_MODULES``
       (default: ``32``).
   * - ``-W, --data-width``
     - The ``HBM_DATA_WIDTH`` of the build (default: ``256``). A wrong value scales every
       reported speed by the same factor.
   * - ``-F, --freq``
     - Frequency of ``HBM_CLK`` in MHz (default: ``450``). The counters are converted to
       seconds with it, so it scales both the speed and the latency results.

Register Map
^^^^^^^^^^^^

.. list-table::
   :header-rows: 1
   :widths: 15 25 60

   * - Offset
     - Name
     - Description
   * - ``0x00``
     - **Version**
     - ``HBM_TESTER`` version.
   * - ``0x10``
     - **Port Enable**
     - One-hot bitmask to enable/run specific ports.
   * - ``0x14``
     - **Config**
     - Configuration register (see the bitfield below).
   * - ``0x18``
     - **Reset**
     - Writing to this register resets the tester logic.
   * - ``0x1C``
     - **Duration**
     - Test duration (limit defined by ``CNT_WIDTH``).
   * - ``0x20``
     - **Status**
     - Monitoring done / stats ready of each port (one-hot address).
   * - ``0x200``
     - **Stats 0**
     - Base address for counter 0.
   * - ``0x204``
     - **Stats 1**
     - Base address for counter 1.

Configuration Register (0x14) Bitfield
""""""""""""""""""""""""""""""""""""""

.. list-table::
   :header-rows: 1
   :widths: 12 20 68

   * - Bits
     - Function
     - Description
   * - ``[0]``
     - Connection
     - 0 = user source, 1 = generator source.
   * - ``[1]``
     - Addr Mode
     - 0 = sequential, 1 = pseudorandom.
   * - ``[2]``
     - Dead Data
     - 0 = counter value, 1 = ``0xDEADCAFE``.
   * - ``[3]``
     - R/W Switch
     - Enable automatic R/W toggling.
   * - ``[5:4]``
     - Run Mode
     - 00 = none, 01 = WR only, 10 = RD only, 11 = RD and WR.
   * - ``[6]``
     - Burst Mode
     - Length of one burst in bus words: 0 = 1 word, 1 = 2 words. On a 256b bus that is
       BL4 (32B) and BL8 (64B), on a 512b bus 64B and 128B.
   * - ``[7]``
     - R/W No Wait
     - 0 = wait for the write response before reading the same address, 1 = read
       immediately. See `Read after Write`_.
   * - ``[10:8]``
     - Counter 0 Mode
     - Selects the metric for result counter 0 (see below).
   * - ``[14:12]``
     - Counter 1 Mode
     - Selects the metric for result counter 1 (see below).

**Counter modes**

* ``000`` -- read words count
* ``001`` -- write words count
* ``010`` -- read latency
* ``011`` -- write latency
* ``100`` -- data OK count
* ``101`` -- data error count
