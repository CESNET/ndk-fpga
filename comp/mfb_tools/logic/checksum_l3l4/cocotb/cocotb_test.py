# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter

from testbench import Testbench


@cocotb.test()
async def run_test_base(dut, pkt_count=1000):
    """Base test with random gaps and backpressure, random packet sizes 60-8000B"""
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 base test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # Initialize testbench
    tb = Testbench(dut, debug=False)

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # Set up idle generators for both drivers to create gaps
    #tb.mfb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))
    tb.mvb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))

    # Start backpressure (randomized DST_RDY)
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    # Generate and send packets with random sizes 60-8000B
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=60, max_len=8000)

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

    # Displaying result of the test
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_full_speed(dut, pkt_count=1000):
    """Full speed test without gaps and backpressure, random packet sizes 60-8000B"""
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 full speed test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # Initialize testbench
    tb = Testbench(dut, debug=False)

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # No idle generators - full speed
    # No backpressure - full speed on output
    dut.TX_MVB_DST_RDY.value = 1

    # Generate and send packets with random sizes 60-8000B
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=60, max_len=8000)

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

    # Displaying result of the test
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_small_pkt(dut, pkt_count=1000):
    """Small packets test with gaps and backpressure, packet sizes up to 128B"""
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 small packets test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # Initialize testbench
    tb = Testbench(dut, debug=False)

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # Set up idle generators for both drivers to create gaps
    #tb.mfb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))
    tb.mvb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))

    # Start backpressure (randomized DST_RDY)
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    # Generate and send small packets up to 128B
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=60, max_len=128)

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

    # Displaying result of the test
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_big_pkt(dut, pkt_count=1000):
    """Big packets test with gaps and backpressure, packet sizes above 2000B"""
    cocotb.log.info("Starting MFB_CHECKSUM_L3L4 big packets test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # Initialize testbench
    tb = Testbench(dut, debug=False)

    # Run reset
    await tb.reset()
    cocotb.log.info("Reset completed")

    # Set up idle generators for both drivers to create gaps
    #tb.mfb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))
    tb.mvb_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))

    # Start backpressure (randomized DST_RDY)
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    # Generate and send big packets above 2000B
    for _ in range(pkt_count):
        await tb.generate_and_send_packet(min_len=2001, max_len=8000)

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

    # Displaying result of the test
    raise tb.scoreboard.result
