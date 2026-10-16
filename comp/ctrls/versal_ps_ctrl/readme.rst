.. _versal_ps_ctrl:

VERSAL_PS_CTRL
--------------

.. vhdl:autoentity:: VERSAL_PS_CTRL

The component gives the FPGA design and the host software access to the Processing System (PS) of AMD Versal devices.
It is mainly intended for booting and flashing of Versal based cards, but it provides three independent services:

* **FPGA ID** -- after reset, the component reads the 128-bit device DNA from the PS and provides it on the ``FPGA_ID`` output (e.g. for licensing).
* **PS address space access** -- the host software (MI bus) can read and write any address of the PS/NoC address space through a 2 KB window.
  This is used, for example, to access the boot flash controller.
* **BMC mailbox** -- four registers shared by the host software (MI bus) and the firmware running on the PS (BMC), which the PS accesses through an AXI4-Lite slave port.

Read :ref:`MI bus specification<mi_bus>` for more information on the MI bus.

Architecture
^^^^^^^^^^^^

.. code-block:: text

           CLK domain  :  AXI_LITE_CLK domain
                       :
    MI (slave) ---> MI_ASYNC ----------------> +--------------------+
                       :                       |  VERSAL_PS_ACCESS  |  AXI4 (S1)  +-------------------+
    AXI_LITE (slave) --:--> AXI4LITE2MI -----> |  registers,        |------------>|                   |
    from PS            :          (MI_PS)      |  2 KB window       |             |                   |
                       :                       +--------------------+             | VERSAL_AXI_SWITCH |---> AXI4 (master)
                       :                                 ^ ENABLE                 |                   |     to PS
                       :                                 |           AXI4 (S0)    |                   |
                       :       VERSAL_FPGA_ID -----------|----------------------->|                   |
                       :            |                    |                        +-------------------+
                       :            | FPGA_ID, VLD       | VLD                              ^ SEL = VLD
    FPGA_ID,     <-- SYNC_FPGA_ID <-+--------------------+----------------------------------+
    FPGA_ID_VLD        :

The component consists of the following subcomponents:

* ``VERSAL_FPGA_ID`` -- reads the device DNA after reset through its own AXI4 master (:ref:`MI2AXI4<mi2axi4>`).
* ``VERSAL_PS_ACCESS`` -- the register block and the address window for the host software.
  It contains an :ref:`MI_SPLITTER_PLUS_GEN<mi_splitter_plus_gen>` (registers / window) and an :ref:`MI2AXI4<mi2axi4>` for the window accesses.
* ``VERSAL_AXI_SWITCH`` -- a simple multiplexer of the two AXI4 masters.
  It does not track transactions; the masters must not be active at the same time, which is ensured by the switching rule below.
* ``SYNC_FPGA_ID`` -- transfers the FPGA ID from ``AXI_LITE_CLK`` to ``CLK``.
* ``AXI4LITE2MI`` -- converts the AXI4-Lite slave port used by the PS to the internal MI bus of the BMC mailbox registers.
* :ref:`MI_ASYNC<mi_async>` -- transfers the MI bus of the host software from ``CLK`` to ``AXI_LITE_CLK``.

Clocks and resets
~~~~~~~~~~~~~~~~~

* ``CLK`` / ``RESET`` -- clock domain of the MI slave port and of the ``FPGA_ID`` / ``FPGA_ID_VLD`` outputs.
* ``AXI_LITE_CLK`` / ``AXI_LITE_RESET`` -- clock domain of both AXI interfaces to the PS and of all internal logic.

Both resets are active high.
The two clock domains are independent; the component contains the clock domain crossings.

FPGA ID
^^^^^^^

After ``AXI_LITE_RESET`` is released, ``VERSAL_FPGA_ID`` reads four 32-bit words of the device DNA from the PMC eFUSE cache (base address ``0xF125_0000``) of the PS:

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - PS address
     - ``FPGA_ID`` bits
   * - ``0xF125_0020``
     - ``FPGA_ID(31 downto 0)``
   * - ``0xF125_0024``
     - ``FPGA_ID(63 downto 32)``
   * - ``0xF125_0028``
     - ``FPGA_ID(95 downto 64)``
   * - ``0xF125_002C``
     - ``FPGA_ID(127 downto 96)``

When the last word is read, the internal FPGA ID valid flag is set and stays set until the next ``AXI_LITE_RESET``.
The ID is read only once after each reset.

The flag also controls the rest of the component:

* Until it is set, the AXI4 master port is connected to ``VERSAL_FPGA_ID`` and accesses to the address window wait (``BUSY`` is reported, see below).
* Once it is set, the AXI4 master port is switched to ``VERSAL_PS_ACCESS`` permanently.

``SYNC_FPGA_ID`` transfers the ID to the ``CLK`` domain.
``FPGA_ID_VLD`` goes high a few ``CLK`` cycles after ``FPGA_ID`` has settled in the ``CLK`` domain, so ``FPGA_ID`` is stable while ``FPGA_ID_VLD`` is asserted.
The exception is ``AXI_LITE_RESET``: it clears the ID, and ``FPGA_ID`` changes to 0 a few ``CLK`` cycles before ``FPGA_ID_VLD`` falls, because the valid flag has the longer synchronizer.
Capture ``FPGA_ID`` on the rising edge of ``FPGA_ID_VLD``.

.. note::
   The AXI read responses (``RRESP``) are not checked.
   If the PS returns an error for the DNA reads (e.g. the PS port has no access to the eFUSE cache), ``FPGA_ID_VLD`` is asserted anyway and ``FPGA_ID`` contains the returned data.

Host software interface (MI)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The MI slave port occupies 4 KB (``0x1000`` bytes) of the MI address space.
Only the lowest 12 address bits are decoded: ``MI_ADDR(11)`` selects between the register block and the address window, ``MI_ADDR(10 downto 0)`` select the register or the offset in the window.

.. list-table::
   :header-rows: 1
   :widths: 14 22 8 56

   * - Offset
     - Register
     - Access
     - Description
   * - ``0x000``
     - STATUS
     - R
     - Bit 0: ``BUSY``.
       Bit 1: ``ADDR64`` -- the PS address is 64 bits wide (``AXI_ADDR_WIDTH_INT = 64``) and UPPER_ADDR is used.
       Other bits read as 0.
   * - ``0x004``
     - UPPER_ADDR
     - R/W
     - Bits 63:32 of the PS address of the window (used only when ``ADDR64`` = 1).
   * - ``0x008``
     - LOWER_ADDR
     - R/W
     - Bits 31:0 of the PS address of the window.
       Only bits 31:11 are used, the window is aligned to 2 KB; bits 10:0 are stored but ignored.
   * - ``0x00C``
     - BMC_STATUS
     - R/W
     - BMC mailbox register, see `BMC mailbox`_.
   * - ``0x010``
     - BMC_CONTROL
     - R/W
     - BMC mailbox register.
   * - ``0x014``
     - BMC_ERASE_START
     - R/W
     - BMC mailbox register.
   * - ``0x018``
     - BMC_ERASE_SIZE
     - R/W
     - BMC mailbox register.
   * - ``0x01C`` -- ``0x7FC``
     - --
     - R
     - Reserved, reads as 0.
   * - ``0x800`` -- ``0xFFF``
     - Address window
     - R/W
     - 2 KB window into the PS address space, see `Address window`_.

Writes to the registers ignore ``MI_BE``; the whole 32-bit word is always written.
The registers decode ``MI_ADDR(10 downto 0)`` including the two lowest bits, so only word aligned addresses access them.
UPPER_ADDR and LOWER_ADDR are cleared by ``AXI_LITE_RESET``.
The BMC mailbox registers are not reset (they are cleared only at configuration).

Address window
~~~~~~~~~~~~~~

An MI access to offset ``0x800 + N`` (``N`` = ``0x000`` -- ``0x7FC``) is translated to a single AXI4 access of the PS address:

* ``AXI_ADDR_WIDTH_INT = 32``: ``LOWER_ADDR(31 downto 11) & N(10 downto 0)``
* ``AXI_ADDR_WIDTH_INT = 64``: ``UPPER_ADDR & LOWER_ADDR(31 downto 11) & N(10 downto 0)``

The two lowest address bits are always zero (word access).
For example, with LOWER_ADDR = ``0x8000_1234``, an MI write to offset ``0x810`` writes PS address ``0x8000_1010`` and offset ``0xFFC`` maps to ``0x8000_17FC``.

Properties of the AXI4 accesses (on the AXI4 master port):

* Single-beat 32-bit transfers: ``AxLEN`` = 0, ``AxSIZE`` = 4 bytes, ``AxBURST`` = INCR, ``WLAST`` = 1.
* ``WSTRB`` is taken from ``MI_BE``.
* ``AxID`` = 0, ``AxPROT`` = ``"000"``, ``AxCACHE`` = ``"0000"``, ``AxLOCK`` = 0, ``AxQOS`` = ``"0000"``.
* ``AWUSER`` = ``WRITE_SMID`` and ``ARUSER`` = ``READ_SMID`` (System Management ID of the PL master).
* One transaction at a time; an MI read is answered only after the AXI read data arrive.
* The AXI responses (``BRESP``, ``RRESP``) are not checked; an access that ends with an AXI error is completed on MI normally (a read returns the AXI read data as they are).

The ``BUSY`` bit is set while the FPGA ID has not been read yet, while a window write accepted on the MI bus has not been issued on the AXI write address channel yet, or while a window read has not been completed.
``AXI_LITE_RESET`` drops the pending window accesses and clears this state.
The address of a window access is composed when it is issued on the AXI bus, from the current values of UPPER_ADDR and LOWER_ADDR.
Therefore, software must wait for ``BUSY`` = 0 before it changes UPPER_ADDR or LOWER_ADDR; otherwise, a pending access can be issued to the new address.

.. warning::
   The address window and its registers are shared by all users of the component.
   All software accesses must be serialized (locked) by the software; mixing accesses from multiple processes can lead to data corruption.

.. warning::
   There is no timeout. If the PS port does not respond to an AXI access, the window access never completes and the MI bus stays blocked.
   ``AXI_LITE_RESET`` recovers from this state: :ref:`MI_ASYNC<mi_async>` answers a pending MI read with ``0xDEADFEED`` and the component starts again by reading the FPGA ID.

BMC mailbox
^^^^^^^^^^^

The four BMC registers are accessible both from the host software (MI, offsets ``0x00C`` -- ``0x018``) and from the PS through the AXI4-Lite slave port:

.. list-table::
   :header-rows: 1
   :widths: 25 20 20 35

   * - Register
     - MI offset
     - PS offset
     - Simultaneous writes
   * - BMC_STATUS
     - ``0x00C``
     - ``0x000``
     - PS write wins
   * - BMC_CONTROL
     - ``0x010``
     - ``0x004``
     - MI write wins
   * - BMC_ERASE_START
     - ``0x014``
     - ``0x008``
     - MI write wins
   * - BMC_ERASE_SIZE
     - ``0x018``
     - ``0x00C``
     - MI write wins

The meaning of the register contents is defined by the communication protocol between the software driver and the BMC firmware; the hardware only stores the values.
The protocol must avoid simultaneous writes to the same register from both sides, otherwise one of the writes is lost.

On the PS side, only ``AXI_LITE_xxADDR(10 downto 0)`` are decoded, so the four registers repeat every 2 KB.
The PS must use 32-bit accesses to word aligned addresses.
``AXI4LITE2MI`` passes the AXI address unchanged and the two lowest bits are decoded too, so an access to an unaligned address (e.g. a byte write to offset ``0x005``) does not reach any register.
``AXI_LITE_WSTRB`` is ignored; a write always stores the whole ``AXI_LITE_WDATA`` word.
Other offsets read as 0 and writes to them are ignored.
All AXI4-Lite responses are OKAY.
The AXI4-Lite port has no protection signals (``AxPROT``) and processes one transaction at a time, reads before writes.

Configuration
^^^^^^^^^^^^^

The widths of the AXI4 master port depend on the PS port the component is connected to.
For the PS Slave AXI LPD interface (the defaults), use ``AXI_ADDR_WIDTH`` = 49, ``AXI_ID_WIDTH`` = 6 and ``AXI_ARUSER_WIDTH`` = ``AXI_AWUSER_WIDTH`` = 10.

``READ_SMID`` and ``WRITE_SMID`` set the System Management ID of the component as a PS master.
The value must be unique among the PL masters of the design; the two values may be the same.
On the Slave AXI LPD interface, the highest SMID bit must be 0 to indicate a PL master; the component checks this with an assertion when the USER width is 10.
See the Versal documentation for the SMID rules of other ports.

``AXI_ADDR_WIDTH_INT`` selects the internal PS address width: 32 for access through the LPD/FPD interfaces, 64 for access through the NoC.
The internal address is zero-extended or truncated to ``AXI_ADDR_WIDTH`` on the AXI4 master port.

``AXI_DATA_WIDTH`` must be 32.

Device Tree
^^^^^^^^^^^

``DevTree.tcl`` provides the procedure ``dts_boot_controller {base type}``, which generates the node:

.. code-block:: text

    boot_controller {
        compatible = "dynanic,versal_ps_bridge";
        reg = <base 0x1000>;
    };

The ``type`` argument is currently not used.

Verification
^^^^^^^^^^^^

The component is verified with cocotb in the ``cocotb/`` directory.
The host software drives the MI port, the BMC firmware the AXI4-Lite port (``AxiLiteMaster`` from `cocotbext-axi <https://github.com/alexforencich/cocotbext-axi>`_), and a PS model terminates the AXI4 master port with configurable ready rates, response latency and error responses.
The PS model checks the AXI4 protocol of the master port (handshake stability, single-beat transfers, the fixed sideband values, SMIDs in ``AxUSER`` and one transaction at a time).
A cycle accurate model of the register block observes the host and PS writes at the inputs of the registers, including simultaneous writes, and every read is compared end to end with the value delivered on the external ports.
The window accesses are compared with the expected AXI transactions, ``BUSY`` is checked against the window accesses still pending, and ``FPGA_ID`` against the DNA words returned by the PS.

The tests cover concurrent host and BMC traffic in several PS timing, error and clock ratio scenarios, the FPGA ID sequence and its resets, window accesses before the FPGA ID is read, the register map, the window address translation, strobes, error responses, ``BUSY``, the BMC mailbox with its aliases and simultaneous writes, and the recovery by ``AXI_LITE_RESET``.
``ver_settings.py`` adds the 64-bit internal address, other AXI address, ID and USER widths.

.. code-block:: bash

    cd cocotb
    make cocotb-venv
    source venv-VERSAL_PS_CTRL/bin/activate
    make
