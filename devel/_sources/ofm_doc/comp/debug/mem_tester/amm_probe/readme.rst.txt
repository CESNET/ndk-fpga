.. _amm_probe:

AMM_PROBE
---------

AMM_PROBE is now depreciated and :ref:`MEM_LOGGER<mem_logger>` should be used!
AMM_PROBE listens to the AMM bus and measures:

- Written / read AMM words and read requests count
- Number of ticks (CLK cycles) from the first to the last write request (same for read requests)
- Number of ticks (CLK cycles) of the whole communication (from the first r/w req to the last r/w req)
- Average, minimal and maximal latency of read requests
- Latency histogram of read requests

MI Bus Control
^^^^^^^^^^^^^^

**MI Address Space Definition**

.. code-block::

    BASE + 0x00 -- ctrl
                  0. bit -- reset
                  1. bit -- latency to first received word
                  2. bit -- write ticks overflow occurred
                  3. bit -- read  ticks overflow occurred
                  4. bit -- r/w   ticks overflow occurred
                  5. bit -- write words overflow occurred
                  6. bit -- read words  overflow occurred
                  7. bit -- read req    overflow occurred
                  8. bit -- latency ticks overflow occurred
                  9. bit -- latency counters overflow occurred
                  10. bit -- latency sum overflow occurred
                  11. bit -- latency histogramer counters overflow occurred
                  12. bit -- latency histogramer is linear occurred
    BASE + 0x04 -- write ticks
    BASE + 0x08 -- read  ticks
    BASE + 0x0C -- r/w   ticks
    BASE + 0x10 -- written words
    BASE + 0x14 -- read    words
    BASE + 0x18 -- read request made
    BASE + 0x1C -- latency sum (2x MI registers)
    BASE + 0x24 -- latency min
    BASE + 0x28 -- latency max
    BASE + 0x2C -- latency hist cnt
    BASE + 0x20 -- latency hist sel
    BASE + 0x34 -- AMM data width
    BASE + 0x38 -- AMM address width
    BASE + 0x3C -- AMM burst width
    BASE + 0x40 -- AMM freq [kHz]
    BASE + 0x44 -- latency ticks width
    BASE + 0x48 -- histogramer counters cnt
