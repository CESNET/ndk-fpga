# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

from cocotbext.ofm.avmm.drivers import AvalonMMDriverMaster
from cocotbext.ofm.avmm.config import AvalonMMParams, AvalonMMDataUnits
from cocotbext.ofm.utils.ram import RAM


# definition of the class encapsulating components of the test
class testbench():
    # dut = device tree of the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut

        # setting up the Avalon-MM master driving the DUT.
        # The AVMM_BRAM is a simple sequential component: it uses READY
        # (not WAITREQUEST), processes one request at a time (no pipelining),
        # has a fixed read latency of 1 cycle (BRAM output register) and
        # addresses in words.
        avmm_params = AvalonMMParams(
            addressUnits=AvalonMMDataUnits.words,
            maximumPendingReadTransactions=1,  # no read pipelining
            maximumPendingWriteTransactions=0,  # no write responses
            readLatency=1,                      # SDP_BRAM_BEHAV OUTPUT_REG=True
            readWaitTime=0,
            writeWaitTime=0,
        )
        self.master: AvalonMMDriverMaster = AvalonMMDriverMaster(self.dut, "AVMM", dut.CLK, params=avmm_params)

        # golden reference model of the memory (byte addressed)
        self.model_ram: RAM = RAM(2**len(dut.AVMM_ADDRESS) * (len(dut.AVMM_WRITEDATA) // 8))

    # method performing a hardware reset
    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


# defining a test - functions with "@cocotb.test()" decorator will be automatically found and run
@cocotb.test()
async def run_test(dut, pkt_count=10_000):
    # start a clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    # initialization of the test bench
    tb = testbench(dut, debug=False)

    # running simulated reset
    await tb.reset()

    word_bytes = len(dut.AVMM_WRITEDATA) // 8

    # simple directed test: write random data to random addresses and read them back
    from random import randint, seed
    seed(42)

    for i in range(pkt_count):
        address = randint(0, 2**len(dut.AVMM_ADDRESS) - 1)
        data    = randint(0, 2**(8 * word_bytes) - 1)

        # write through the master driver and into the reference model
        await tb.master.write(address, data.to_bytes(word_bytes, "little"))
        tb.model_ram.wint(address * word_bytes, data, word_bytes)

        # read back and compare with the reference model
        response = await tb.master.read(address)
        expected = tb.model_ram.rint(address * word_bytes, word_bytes)
        received = int.from_bytes(response.data, "little")

        assert received == expected, \
            f"Data mismatch at address {address:#x}: expected {expected:#x}, received {received:#x}"

    cocotb.log.info(f"All {pkt_count} write/read transactions passed.")
