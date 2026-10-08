# cocotb_test.py: DRAM_FIFO cocotb test
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotb.types import Logic, LogicArray

from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.protocol import Axi4StreamProtocol
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.base.protocol import alias
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator
from cocotbext.ofm.base.generators import EthernetRateLimiter
from cocotbext.ofm.utils.ram import RAM
from cocotbext.ofm.avmm.drivers import AvalonMMDriverSlave
from cocotbext.ofm.avmm.config import AvalonMMParams
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeInterface

# Note: This test uses DRAM_FIFO as the top-level entity.


class Axi4sDramFifoProtocol(Axi4StreamProtocol):
    """DRAM_FIFO names its AXI ports without the AXI4-Stream ``T`` prefix
    (``RX_AXI_DATA`` rather than ``RX_AXI_TDATA``). Each alias is tried after
    the canonical name fails to resolve on the bus.
    """
    DATA  : LogicArray = alias(Axi4StreamProtocol.TDATA)
    VALID : Logic      = alias(Axi4StreamProtocol.TVALID)
    READY : Logic      = alias(Axi4StreamProtocol.TREADY)
    LAST  : Logic      = alias(Axi4StreamProtocol.TLAST)
    KEEP  : LogicArray = alias(Axi4StreamProtocol.TKEEP)


class Axi4StreamMasterV(Axi4StreamMaster):
    bus: Axi4sDramFifoProtocol

    def __init__(self, *args, protocol=Axi4sDramFifoProtocol, **kwargs):
        super().__init__(*args, protocol=protocol, **kwargs)


class Axi4StreamV(Axi4Stream):
    _signals = {"TVALID": "VALID"}
    _optional_signals = {"TREADY": "READY", "TDATA": "DATA", "TLAST": "LAST", "TKEEP": "KEEP", "TUSER": "USER"}


class ThroughputProbeAxi4StreamInterface(ThroughputProbeInterface):
    interface_dict = {
        "clock"     : "clock",
        "in_reset"  : None,
        "items"     : None,
        "item_width": None,
        "item_cnt"  : None,
    }

    def __init__(self, agent):
        super().__init__(agent)
        self._beat_cnt = 0

    @property
    def in_reset(self):
        return False

    @property
    def items(self):
        # One beat can be transferred per clock cycle.
        return 1

    @property
    def item_width(self):
        return len(self._agent.bus.TDATA)

    @property
    def item_cnt(self):
        return self._beat_cnt

    def count_transfer(self):
        """Call this once per clock when a valid transfer occurs."""
        self._beat_cnt += 1


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut

        # AXI interface for RX (write to DRAM_FIFO) - data come into DUT from here
        self.axi_rx_drv = Axi4StreamMasterV(dut, "RX_AXI", dut.CLK)

        # AXI interface for TX (read from DRAM_FIFO)
        self.axi_tx_drv = BitDriver(dut.TX_AXI_READY, dut.CLK)
        self.axi_tx_mon = Axi4StreamV(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)
        self.axi_rx_mon = Axi4StreamV(dut, "RX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut, fail_immediately=False)
        self.scoreboard.add_interface(self.axi_tx_mon, self.expected_output)

        # AVMM memory model (external DRAM)
        self.mem_ram = RAM(0x08000000)
        self.mem_slave = AvalonMMDriverSlave(dut, "AVMM", dut.CLK,
                                             params=AvalonMMParams(),
                                             ram=self.mem_ram)

        self.tx_throughput_interface = ThroughputProbeAxi4StreamInterface(self.axi_tx_mon)
        self.tx_throughput_probe = ThroughputProbe(
            self.tx_throughput_interface,
            throughput_units="bits",
            name="ThroughputProbe - TX"
        )
        self.tx_throughput_probe.add_log_interval(0, None)  # from start to end of simulation
        self.tx_throughput_probe.set_log_period(1)         # log every 1 us

        self.rx_throughput_interface = ThroughputProbeAxi4StreamInterface(self.axi_rx_mon)
        self.rx_throughput_probe = ThroughputProbe(
            self.rx_throughput_interface,
            throughput_units="bits",
            name="ThroughputProbe - RX"
        )

        self.rx_throughput_probe.add_log_interval(0, None)  # from start to end of simulation
        self.rx_throughput_probe.set_log_period(1)          # log every 1 us

        # Run a small helper coroutine that tells the byte-count interface
        # whenever a data beat is transferred on TX_AXI.
        cocotb.start_soon(self._throughput_counter(self.axi_tx_mon, self.tx_throughput_interface))
        cocotb.start_soon(self._throughput_counter(self.axi_rx_mon, self.rx_throughput_interface))

    def model(self, tr: Axi4StreamTransaction):
        """Model of the DUT - stores expected output for scoreboard comparison"""
        self.expected_output.append(tr)
        self.pkts_sent += 1

    async def _throughput_counter(self, axi_mon, interface):
        """Count valid TX_AXI data beats for the throughput probe."""
        while True:
            await RisingEdge(self.dut.CLK)
            if (
                axi_mon.bus.TVALID.value.is_resolvable and
                axi_mon.bus.TREADY.value.is_resolvable and
                int(axi_mon.bus.TVALID.value) and
                int(axi_mon.bus.TREADY.value)
            ):
                interface.count_transfer()

    async def reset(self):
        """Reset the DUT"""
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, frame_count=10000, frame_size_min=100, frame_size_max=4096):
    """
    Main test function for DRAM_FIFO.

    Args:
        dut: Device under test
        frame_count: Number of packets to send
        frame_size_min: Minimum packet size in bytes
        frame_size_max: Maximum packet size in bytes
    """
    dut.RESET.value = 1
    # Start CLK
    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())

    tb = testbench(dut)

    rl = EthernetRateLimiter(bitrate=500_000)
    rl.configure(clk_freq=200_000_000, bits_per_word=tb.dut.AXI_DATA_WIDTH.value)
    tb.axi_rx_drv.set_idle_generator(rl)
    await tb.reset()

    dut.DDR_READ_EN.value = 1

    cocotb.log.info("\n--- Beginning the test ---\n")

    # Start TX ready driver with backpressure
    config = BackpressureConfig(low_prob=0.3)
    gen = BackpressureGenerator(config)
    tb.axi_tx_drv.start(gen)
    await ClockCycles(tb.dut.CLK, 10)

    # Send random packets through RX AXI
    for pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        # packet to axi transaction
        cocotb.log.info(f"TRANSACTION data: {pkt.hex()}")
        axi_tr = Axi4StreamTransaction()
        axi_tr.TDATA = pkt

        # Send to Driver (DUT)
        tb.axi_rx_drv.append(axi_tr)

        # Send to Model (for scoreboard comparison)
        tb.model(axi_tr)

    await ClockCycles(tb.dut.CLK, 1000000)

    # Wait until all packets are received
    last_num = -1
    while (this_num := tb.axi_tx_mon.frame_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.axi_tx_mon.frame_cnt}")
        await ClockCycles(dut.CLK, 10000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    cocotb.log.info(f"Packets sent: {tb.pkts_sent}, Packets received: {tb.axi_tx_mon.frame_cnt}")

    tb.tx_throughput_probe.log_max_throughput()
    tb.tx_throughput_probe.log_average_throughput()

    raise tb.scoreboard.result
