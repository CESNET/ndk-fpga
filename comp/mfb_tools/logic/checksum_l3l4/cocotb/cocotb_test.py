# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig

from testbench import Testbench


@cocotb.test()
async def run_test_base(dut, pkt_count=4000, truncate_chance=0):
    """Base test with random gaps, backpressure, and random packet sizes 60-8000B.

    Args:
        dut: Device Under Test
        pkt_count: Number of packets to send (default: 4000)
        truncate_chance: Probability of truncating packets (default: 0)
    """
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 base test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    # Initialize testbench
    tb = Testbench(dut, debug=False)

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # Start backpressure (randomized DST_RDY)
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # Generate and send packets
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=60, max_len=8000, truncate_chance=truncate_chance)

    # Wait for all packets to be processed
    last_num = 0
    while tb.mvb_tx_monitor.item_cnt < pkt_count:
        if (tb.mvb_tx_monitor.item_cnt // 100) > last_num:
            last_num = tb.mvb_tx_monitor.item_cnt // 100
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.mvb_tx_monitor.item_cnt, pkt_count))
        await ClockCycles(dut.CLK, 10)

    cocotb.log.info(f"Test completed: {tb.mvb_tx_monitor.item_cnt}/{pkt_count} packets processed")

    # Logging values measured by throughput probe
    tb.throughput_probe.log_max_throughput()
    tb.throughput_probe.log_average_throughput()

    # Check scoreboard results
    if tb.scoreboard_errors:
        raise AssertionError(f"Scoreboard comparison failed with {len(tb.scoreboard_errors)} errors")
    cocotb.log.info(f"Scoreboard comparison passed: {tb.scoreboard_comparisons} transactions compared")


@cocotb.test()
async def run_test_corrupted_extreme(dut, pkt_count=5000, truncate_chance=0.9, log_comparisons=False):
    """Test with extreme truncated (corrupted) packets, 90% truncation rate.

    This test verifies circuit functionality with corrupted packets by checking
    if the number of output packets matches the number of sent packets to detect
    circuit hangs. Scoreboard comparison is performed but error logging is
    disabled by default to reduce output noise.

    Args:
        dut: Device Under Test
        pkt_count: Number of packets to send (default: 5000)
        truncate_chance: Probability of truncating packets (default: 0.9)
        log_comparisons: If True, log detailed comparison errors (default: False)
    """
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 extreme corrupted packets test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    # Initialize testbench with disabled comparison logging
    tb = Testbench(dut, debug=False, log_comparisons=log_comparisons)
    tb.stop_on_error = False  # Continue test even on checksum mismatches

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # Start backpressure (randomized DST_RDY)
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # Generate and send packets with extreme truncation (90%)
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=60, max_len=8000, truncate_chance=truncate_chance)

    # Wait for all packets to be processed with timeout to detect hangs
    timeout_cycles = 0
    max_timeout_cycles = pkt_count * 1000  # Reasonable timeout
    last_num = 0
    while tb.mvb_tx_monitor.item_cnt < pkt_count:
        if (tb.mvb_tx_monitor.item_cnt // 100) > last_num:
            last_num = tb.mvb_tx_monitor.item_cnt // 100
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.mvb_tx_monitor.item_cnt, pkt_count))
        await ClockCycles(dut.CLK, 10)
        timeout_cycles += 10

        if timeout_cycles > max_timeout_cycles:
            raise AssertionError(f"Test timeout: only {tb.mvb_tx_monitor.item_cnt}/{pkt_count} packets processed")

    cocotb.log.info(f"Test completed: {tb.mvb_tx_monitor.item_cnt}/{pkt_count} packets processed")

    # Logging values measured by throughput probe
    tb.throughput_probe.log_max_throughput()
    tb.throughput_probe.log_average_throughput()

    # Verify packet count matches (detect circuit hangs)
    if tb.mvb_tx_monitor.item_cnt != pkt_count:
        raise AssertionError(f"Packet count mismatch: sent {pkt_count}, received {tb.mvb_tx_monitor.item_cnt}")

    cocotb.log.info(f"Packet count verification passed: {pkt_count} packets sent and received")
