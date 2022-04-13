.. _mem_tester_amm_probe:

AMM_PROBE
---------

This component is used to listen to the AMM bus and measure:

- Written / read AMM words and read requests count
- Number of ticks (CLK cycles) from the first to the last write request (same for read requests)
- Number of ticks (CLK cycles) of the whole communication (from the first r/w req to the last r/w req)
- Average, minimal and maximal latency of read requests - NOT DONE YET

Internal Architecture
^^^^^^^^^^^^^^^^^^^^^

MI Bus Control
^^^^^^^^^^^^^^

**MI Address Space Definition**

.. code-block::

    BASE + 0x00 -- ctrl
                  0. bit -- reset
                  1. bit -- write ticks overflow occurred
                  2. bit -- read  ticks overflow occurred
                  3. bit -- r/w   ticks overflow occurred
                  4. bit -- write words overflow occurred
                  5. bit -- read words  overflow occurred
                  6. bit -- read req    overflow occurred
    BASE + 0x04 -- write ticks
    BASE + 0x08 -- read  ticks
    BASE + 0x0C -- r/w   ticks
    BASE + 0x10 -- written words
    BASE + 0x14 -- read    words
    BASE + 0x18 -- read request made
