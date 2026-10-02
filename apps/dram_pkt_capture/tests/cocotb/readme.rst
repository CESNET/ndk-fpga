.. _dram_pkt_capture_tls:

Top-level simulation
====================

The top-level simulation (TLS) runs the whole ``fpga`` entity — PCIe, DMA,
Ethernet and the application core. It is the only test that exercises the
capture path end to end: Ethernet frames go in at the MAC, and the same bytes
come back out of the host DMA rings.

For the ``DRAM_FIFO`` component on its own, see the component-level cocotb
testbench in ``comp/dram_fifo/cocotb/``.

How it works
------------

The testbench lives in ``tests/cocotb/cocotb_test.py``. It builds an
``NFBDevice`` around the DUT, which gives it a simulated ``nfb`` handle — so the
test drives the design through the same register and DMA API that software uses
on a real card.

Because the memory clock is not driven by any model, the testbench starts it
itself: ``_init_mem_clk_rst()`` runs a 300 MHz clock on every ``mem_clk`` port
and forces ``mem_rst_n`` high. If ``mem_rst_n`` is not visible at the top level
it logs a warning and leaves the reset to the EMIF model.

Register access goes through ``AppStatus`` from
``scripts/dram_pkt_capture_regs.py``, the same class the hardware scripts use.
The Makefile adds ``scripts/`` to ``PYTHONPATH`` so the test can import it.

The main test is ``test_ndp_rcv_msg_multi``, which runs four concurrent tasks:

- a **producer** that pushes random frames (64–500 B, 20000 of them) into the
  Ethernet RX driver of subcore 0, with a random 50–150 ns gap between frames.
- ``log_dram_full()``, which polls ``capture_enable`` once per microsecond.
  Capture is armed at the start, so seeing it *clear* means hardware asserted
  ``dram_full``. That signals the producer to stop and sets ``read_enable`` to
  begin draining.
- ``receive_all()``, which polls every DMA RX channel and collects packets. It
  stops once the ring has drained — ``dram_full`` was seen and 10000 poll
  iterations pass with no new packet — or once every sent frame has arrived.
- ``log_rxmac_stats()``, which prints the RX MAC dropped and overflowed counters
  every 10 µs. A rising drop count means frames were lost before the
  application, not inside it.

The test then asserts that received packets match sent packets in order, that
nothing was duplicated, and that no packet arrived that was never sent. It
deliberately checks for a *subset*: capture stops at ``dram_full``, so frames
still in flight are expected to be missing.

Only **subcore 0** is driven, although ``app_status`` is read for every
Ethernet stream.

Prerequisites
-------------

.. warning::
    ``MEM_TARGET`` in ``application_core.vhd`` must be ``MEM_TGT_BRAM``. The
    card's DDR4 controllers are not bound in simulation, and with
    ``MEM_TGT_EXT_DDR`` the AVMM interface connects to unbound components
    see :ref:`ndk_app_dram_pkt_capture`.

Running
-------

.. code-block:: bash

    cd apps/dram_pkt_capture/tests/cocotb
    make cocotb-venv     # once, creates venv-fpga and installs the test package
    make

``make cocotb-venv`` sources the repository ``env.sh`` and installs
``cocotbext-ofm`` and ``ofm`` from the local ``python/`` tree into
``venv-fpga``.

``CARD`` selects which ``build/<card>/`` directory supplies the design. It
defaults to ``n6010``, the application's only target.


Host DMA buffer sizing
----------------------

The test needs more host-side DMA buffering than the packaged model provides.
Two values in the installed ``cocotbext`` package have to be raised:

.. list-table::
    :header-rows: 1
    :widths: 40 20 20 20

    * - Location
      - Field
      - Shipped
      - Needed
    * - ``cocotbext/nfb/queue.py``
      - ``_buffer_size``
      - ``1 MiB``
      - ``4 MiB``
    * - ``cocotbext/nfb/device.py``
      - ``RAM(...)``
      - ``128 MiB``
      - ``256 MiB``

``_desc_cnt`` is derived as ``_buffer_size // _packet_length_max``, so the
shipped 1 MiB gives only 256 blocks per channel. Exceed that and frames come
back truncated on a 128-byte boundary with a zero tail and a correct length,
which looks like an RTL fault but is not.

.. warning::
    These are edits to the *installed* package inside ``venv-fpga``, not to the
    repository. Re-running ``make cocotb-venv`` reinstalls from ``python/`` and
    reverts them. Check both values before concluding that a truncation bug is
    in the design.
