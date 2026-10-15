.. _axi4lite2mi:

AXI4LITE2MI
-----------

.. vhdl:autoentity:: AXI4LITE2MI

Read :ref:`MI bus specification<mi_bus>` for more information on the MI bus.
Refer to the `AMBA AXI Protocol Specification <https://developer.arm.com/documentation/ihi0022/latest>`_ for more information on the AXI4-Lite interface.

The component allows an AXI4-Lite master (e.g., an embedded processor or a vendor IP core with an AXI4-Lite management port) to access firmware components connected to the MI bus.
It is an AXI4-Lite slave on one side and an MI master on the other side.
It is the counterpart of the :ref:`MI2AXI4<mi2axi4>` converter.

Specification
^^^^^^^^^^^^^

Both interfaces use common clock and reset signals.
``RESET`` is synchronous and active high; it resets only the FSM state, the data/address registers are not reset.

The component processes transactions strictly one at a time (no pipelining, no outstanding transactions).
A new AXI request is accepted only when the previous one has been fully completed, including its AXI response.
Every AXI read is translated to exactly one MI read request and every AXI write to exactly one MI write request.

**Arbitration** -- When both ``AXI_ARVALID`` and ``AXI_AWVALID`` are asserted in the same cycle while the component is idle, the read is served first.
A master issuing reads back-to-back can therefore delay writes.

**Address** -- The AXI address (``AXI_ARADDR`` or ``AXI_AWADDR``) is masked with the ``ADDR_MASK`` generic (bitwise AND), registered and then presented on ``MI_ADDR``.
No other modification is performed (the address is not aligned by the component), so the byte address issued by the AXI master is passed to the MI bus as is.
Follow the :ref:`MI address alignment convention<mi_addr_alignment>` and use addresses aligned to ``DATA_WIDTH/8`` bytes.

**Write data and byte enable** -- ``AXI_WDATA`` and ``AXI_WSTRB`` are registered and presented on ``MI_DWR`` and ``MI_BE``, respectively.
For MI read requests, ``MI_BE`` is set to all ones (the whole data word is read), as AXI4-Lite has no byte strobes for reads.

**Read data** -- ``MI_DRD`` is registered when ``MI_DRDY`` is asserted and returned on ``AXI_RDATA``.

**Responses** -- ``AXI_BRESP`` and ``AXI_RRESP`` are always ``"00"`` (OKAY).
The MI bus provides no means of signalling an error, so ``SLVERR``/``DECERR`` responses are never generated.

**Write channel ordering** -- ``AXI_WREADY`` is asserted only after the write address has been accepted.
The master may assert ``AXI_WVALID`` before, together with, or after ``AXI_AWVALID``, as permitted by the AXI specification; the write data are simply held by the master until the address handshake completes.

**Combinational paths** -- In the idle state ``AXI_ARREADY`` and ``AXI_AWREADY`` depend combinationally on ``AXI_ARVALID`` and ``AXI_AWVALID`` (this is allowed by the AXI specification).
There is no combinational path from the MI inputs to the AXI outputs or from the AXI inputs to the MI outputs.

Supported AXI4-Lite signals
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
   :header-rows: 1
   :widths: 20 80

   * - Channel
     - Signals
   * - Write address (AW)
     - ``AXI_AWADDR``, ``AXI_AWVALID``, ``AXI_AWREADY``
   * - Write data (W)
     - ``AXI_WDATA``, ``AXI_WSTRB``, ``AXI_WVALID``, ``AXI_WREADY``
   * - Write response (B)
     - ``AXI_BRESP``, ``AXI_BVALID``, ``AXI_BREADY``
   * - Read address (AR)
     - ``AXI_ARADDR``, ``AXI_ARVALID``, ``AXI_ARREADY``
   * - Read data (R)
     - ``AXI_RDATA``, ``AXI_RRESP``, ``AXI_RVALID``, ``AXI_RREADY``

The protection signals ``AXI_AWPROT`` and ``AXI_ARPROT`` are not present; leave them unconnected on the master side.
The optional MI metadata port (``MI_MWR``) is not present either.

FSM description
^^^^^^^^^^^^^^^

The whole conversion is controlled by a single FSM with the following states:

.. list-table::
   :header-rows: 1
   :widths: 18 52 30

   * - State
     - Description
     - Next state
   * - ``ST_IDLE``
     - No transaction in progress. If ``AXI_ARVALID`` is asserted, ``AXI_ARREADY`` is asserted in the same cycle, the masked read address is registered and the byte enables are set to all ones.
       Otherwise, if ``AXI_AWVALID`` is asserted, ``AXI_AWREADY`` is asserted and the masked write address is registered.
     - ``ST_READ`` on ``AXI_ARVALID``, else ``ST_WRITE`` on ``AXI_AWVALID``
   * - ``ST_READ``
     - MI read request is issued (``MI_RD`` = 1, ``MI_ADDR`` = registered read address, ``MI_BE`` = all ones) and held until the MI slave asserts ``MI_ARDY``.
       If ``MI_DRDY`` is asserted together with ``MI_ARDY``, ``MI_DRD`` is registered immediately.
     - ``ST_READ_RESP`` on ``MI_ARDY`` and ``MI_DRDY``; ``ST_READ_ARDY`` on ``MI_ARDY`` only
   * - ``ST_READ_ARDY``
     - MI read request has been accepted (``MI_RD`` = 0); waiting for the read data. ``MI_DRD`` is registered when ``MI_DRDY`` is asserted.
     - ``ST_READ_RESP`` on ``MI_DRDY``
   * - ``ST_READ_RESP``
     - Registered read data are presented on the R channel (``AXI_RVALID`` = 1, ``AXI_RRESP`` = OKAY) until the master accepts them.
     - ``ST_IDLE`` on ``AXI_RREADY``
   * - ``ST_WRITE``
     - Write address has been accepted. ``AXI_WREADY`` is asserted; ``AXI_WDATA`` and ``AXI_WSTRB`` are registered when ``AXI_WVALID`` is asserted.
     - ``ST_WRITE_DATA`` on ``AXI_WVALID``
   * - ``ST_WRITE_DATA``
     - MI write request is issued (``MI_WR`` = 1, ``MI_ADDR`` = registered write address, ``MI_DWR``/``MI_BE`` = registered data/strobes) and held until the MI slave asserts ``MI_ARDY``.
     - ``ST_WRITE_RESP`` on ``MI_ARDY``
   * - ``ST_WRITE_RESP``
     - Write response is presented on the B channel (``AXI_BVALID`` = 1, ``AXI_BRESP`` = OKAY) until the master accepts it.
     - ``ST_IDLE`` on ``AXI_BREADY``

The FSM stays in its current state whenever the condition for leaving it is not met.
The state transitions can be summarized as follows:

.. code-block:: text

                   AXI_ARVALID
         +---------------------------> ST_READ ---------------------+
         |                                |                         | MI_ARDY &
         |                                | MI_ARDY &               | MI_DRDY
         |                                | !MI_DRDY                |
         |                                v                         v
         |                          ST_READ_ARDY ------------> ST_READ_RESP
         |                                          MI_DRDY         |
         |                                                          | AXI_RREADY
      ST_IDLE <-----------------------------------------------------+
       |   ^
       |   +----------------------------------------------------+
       |                                                        | AXI_BREADY
       | !AXI_ARVALID & AXI_AWVALID                             |
       v                                                        |
      ST_WRITE ------------> ST_WRITE_DATA ------------> ST_WRITE_RESP
               AXI_WVALID                   MI_ARDY

Timing
^^^^^^

Assuming the MI slave responds immediately (``MI_ARDY`` and ``MI_DRDY`` asserted in the first cycle of the request) and the AXI master is always ready to accept responses (``AXI_RREADY``/``AXI_BREADY`` held high), the transactions take:

* **Read**: 3 clock cycles -- AR handshake (``ST_IDLE``), MI read request (``ST_READ``), R handshake (``ST_READ_RESP``).
  ``AXI_RVALID`` is asserted two cycles after the AR handshake.
* **Write**: 4 clock cycles -- AW handshake (``ST_IDLE``), W handshake (``ST_WRITE``), MI write request (``ST_WRITE_DATA``), B handshake (``ST_WRITE_RESP``).
  ``AXI_BVALID`` is asserted three cycles after the AW handshake.

Every cycle of ``MI_ARDY``/``MI_DRDY`` latency on the MI side and every cycle of ``AXI_WVALID``/``AXI_RREADY``/``AXI_BREADY`` delay on the AXI side extends the transaction accordingly.
Hence, the maximum throughput is one read per 3 cycles or one write per 4 cycles.

.. warning::
   The component has no timeout. If the MI slave never asserts ``MI_ARDY`` (or ``MI_DRDY`` for a read), for example because the address is not mapped to any MI component, the FSM waits forever and the AXI master is blocked.
   Make sure that the whole AXI address range reachable through this component is mapped on the MI side (e.g., by an MI splitter with a default/catch-all port).

.. note::
   The ``DATA_WIDTH`` generic must be set to 32.
   The ``DEVICE`` generic is currently unused and has no effect.

Verification
^^^^^^^^^^^^

The component is verified with cocotb in the ``cocotb/`` directory.
The AXI4-Lite port is driven by ``AxiLiteMaster`` from `cocotbext-axi <https://github.com/alexforencich/cocotbext-axi>`_, the MI port is terminated by an MI slave memory model with configurable ``MI_ARDY`` backpressure and ``MI_DRDY`` latency, including ``MI_DRDY`` in the same cycle as ``MI_ARDY``.
Two independent observers check the DUT: an AXI4-Lite checker on the slave port (handshake rules, one transaction at a time, read priority, ``WREADY`` only after the address handshake, OKAY responses) and the MI slave model on the master port (request held until ``MI_ARDY``, ``MI_BE`` all ones for reads, no new request while a read response is pending).
At the end of every test, a scoreboard compares each AXI beat with its MI request, the returned read data and the final content of the MI memory.

The tests cover a randomized mix of concurrent reads and writes in several backpressure scenarios, write-and-read-back of partial and unaligned accesses, read priority, the order of the AW and W channels, MI read latency and ``MI_ARDY`` stalls, response backpressure, the latency and throughput listed in the Timing section, the full address range, reset during traffic and an idle bus.

.. code-block:: bash

    cd cocotb
    make cocotb-venv
    source venv-AXI4LITE2MI/bin/activate
    make

The number of random transactions per scenario is set by the ``COCOTB_TRANSACTIONS`` environment variable (default 2000).
``ver_settings.py`` lists further generic combinations for ``build/scripts/multi_ver/multi_ver_cocotb.py``; the tests read ``ADDR_WIDTH`` and ``ADDR_MASK`` from the DUT, so any configuration is checked against its own address mapping.

An older directed VHDL testbench is located in the ``sim/`` directory (``sim/testbench.vhd``).
It covers reads with ``MI_DRDY`` asserted together with ``MI_ARDY``, reads with delayed ``MI_DRDY``, reads with delayed ``MI_ARDY``, and writes with ``AXI_WVALID`` asserted after or together with ``AXI_AWVALID`` and with immediate or delayed ``MI_ARDY``.
The testbench is not self-checking; the results have to be inspected in the waveform.
