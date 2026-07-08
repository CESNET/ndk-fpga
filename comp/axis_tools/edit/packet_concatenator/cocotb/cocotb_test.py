# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
from random import getrandbits

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles

from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction, Axi4StreamTransactionWithSelect
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_transactions

from testbench import Testbench


@cocotb.test()
async def run_base_test(dut, min_size=40, max_size=200, pkt_count=10000):
    """Base test with random gaps and backpressure, random packet sizes min_size-max_size."""
    cocotb.log.info("Starting AXIS_PACKET_CONCATENATOR base test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)

    # Set up rate limiters for both input streams
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.rx0_drv.set_idle_generator(ItemRateLimiter(rate_percentage=20, **idle_gen_conf))
    tb.rx1_drv.set_idle_generator(ItemRateLimiter(rate_percentage=90, **idle_gen_conf))

    await tb.reset()

    # Start backpressure
    tb.backpressure.start((1, i % 3) for i in itertools.count())

    # Generate and send transactions using random_transactions generator
    rx0_gen = random_transactions(Axi4StreamTransaction, tb.rx0_drv, "TDATA", min_size, max_size, pkt_count)
    rx1_gen = random_transactions(Axi4StreamTransaction, tb.rx1_drv, "TDATA", 20, 70, pkt_count)

    for i, (rx0_tr, rx1_tr) in enumerate(zip(rx0_gen, rx1_gen)):
        cocotb.log.debug(f"Generated packets iteration #{i}: RX0={len(rx0_tr.TDATA)}B, RX1={len(rx1_tr.TDATA)}B")

        rx0_tr_ce     = Axi4StreamTransactionWithSelect()
        rx0_tr_ce     = rx0_tr
        rx0_tr_ce.SEL = getrandbits(1)

        # Model the expected output
        tb.model(rx0_tr, rx1_tr if rx0_tr_ce.SEL else Axi4StreamTransaction())

        # Send to DUT
        tb.rx0_drv.append(rx0_tr_ce)
        if rx0_tr_ce.SEL:
            tb.rx1_drv.append(rx1_tr)

    await ClockCycles(dut.CLK, 10)

    # Wait for all transactions to be received
    last_num = 0
    while tb.tx_mon.frame_cnt < pkt_count:
        if (tb.tx_mon.frame_cnt // 1000) > last_num:
            last_num = tb.tx_mon.frame_cnt // 1000
            cocotb.log.info(f"Number of transactions processed: {tb.tx_mon.frame_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    cocotb.log.info(f"Test completed: {tb.tx_mon.frame_cnt}/{pkt_count} packets processed")
    raise tb.scoreboard.result


@cocotb.test()
async def run_full_speed_test(dut, min_size=40, max_size=500, pkt_count=10000):
    """Full speed test without gaps and backpressure, random packet sizes min_size-max_size."""
    cocotb.log.info("Starting AXIS_PACKET_CONCATENATOR full speed test")

    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)

    # No idle generators - full speed on input
    # No backpressure - full speed on output
    dut.TX_AXIS_TREADY.value = 1

    await tb.reset()

    # Generate and send transactions using random_transactions generator
    rx0_gen = random_transactions(Axi4StreamTransaction, tb.rx0_drv, "TDATA", min_size, max_size, pkt_count)
    rx1_gen = random_transactions(Axi4StreamTransaction, tb.rx1_drv, "TDATA", 1, 20, pkt_count)

    for i, (rx0_tr, rx1_tr) in enumerate(zip(rx0_gen, rx1_gen)):
        cocotb.log.debug(f"Generated packets iteration #{i}: RX0={len(rx0_tr.TDATA)}B, RX1={len(rx1_tr.TDATA)}B")

        rx0_tr_ce     = Axi4StreamTransactionWithSelect()
        rx0_tr_ce     = rx0_tr
        rx0_tr_ce.SEL = getrandbits(1)

        # Model the expected output
        tb.model(rx0_tr, rx1_tr if rx0_tr_ce.SEL else Axi4StreamTransaction())

        # Send to DUT
        tb.rx0_drv.append(rx0_tr_ce)
        if rx0_tr_ce.SEL:
            tb.rx1_drv.append(rx1_tr)

    await ClockCycles(dut.CLK, 10)

    # Wait for all transactions to be received
    last_num = 0
    while tb.tx_mon.frame_cnt < pkt_count:
        if (tb.tx_mon.frame_cnt // 1000) > last_num:
            last_num = tb.tx_mon.frame_cnt // 1000
            cocotb.log.info(f"Number of transactions processed: {tb.tx_mon.frame_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    cocotb.log.info(f"Test completed: {tb.tx_mon.frame_cnt}/{pkt_count} packets processed")
    raise tb.scoreboard.result
