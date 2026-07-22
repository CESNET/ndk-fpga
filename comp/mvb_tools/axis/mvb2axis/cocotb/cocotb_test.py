# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Generated Environment Integration

import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

# OFM extension imports
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.transaction import MvbTrClassicWithMeta
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_integers

# Performed tests:
# 1. MVB < AXIS, even META
# 2. MVB = AXIS, even META
# 3. MVB > AXIS, even META
# 4. MVB < AXIS, odd META
# 5. MVB = AXIS, odd META
# 6. MVB > AXIS, odd META


class Testbench:
    def __init__(self, dut, debug=False):
        self.dut = dut

        # Custom variables
        self.mvb_width  = int(dut.ITEM_WIDTH.value)
        self.axis_width = int(dut.TDATA_WIDTH.value)

        # 1. Input MVB Driver (Matches prefix RX_MVB_*)
        self.stream_in = MVBDriver(dut, "RX_MVB", dut.CLK)

        # 2. Output AXI4-Stream Monitor (Matches prefix TX_AXIS_*)
        self.stream_out = Axi4Stream(dut, "TX_AXIS", dut.CLK, trans_type=Axi4StreamTransaction)

        # 3. Backpressure Generator on AXIS TREADY
        self.backpressure = BitDriver(dut.TX_AXIS_TREADY, dut.CLK)

        # 4. Scoreboard Tracking
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        # Debug logs setup
        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

    def model(self, mvb_transaction: MvbTrClassicWithMeta):
        """
        Reference Model: Converts an incoming MVB item into the expected
        AXI4-Stream transaction format.
        """
        axi_tr = Axi4StreamTransaction()

        # Get MVB data width in bits and convert to byte length
        item_width_bits = self.stream_in.item_widths["data"]
        meta_width_bits = self.stream_in.item_widths["meta"]
        item_width_bytes = (item_width_bits + 7) // 8
        meta_width_bytes = (meta_width_bits + 7) // 8

        # Number of beats required for axis transaction
        mvb_width  = self.mvb_width
        axis_width = self.axis_width
        axis_transaction_length = (mvb_width + axis_width - 1) // axis_width

        # Convert raw integer MVB data to a byte array
        data_bytes = int(mvb_transaction.data).to_bytes(item_width_bytes, byteorder='little')

        # Initialize with the base transaction metadata
        meta_int = int(mvb_transaction.meta)
        base_meta_bytes = meta_int.to_bytes(meta_width_bytes, byteorder='little')

        if axis_width < mvb_width:
            meta_bytes = base_meta_bytes * axis_transaction_length
        else:
            meta_bytes = base_meta_bytes

        # Assign payload to the AXI Stream Transaction object
        axi_tr.TDATA = data_bytes
        axi_tr.TUSER = meta_bytes

        # Append to verification queue
        self.expected_output.append(axi_tr)
        self.pkts_sent += 1

    async def reset(self):
        """Performs hardware reset using the RST pin"""
        self.dut.RST.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RST.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count=10000):
    # Start a clock generator (e.g., 200 MHz -> 5 ns period)
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    # Initialize Testbench
    tb = Testbench(dut, debug=False)

    # Configure input rate-limiter for the MVB driver
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.stream_in.set_idle_generator(ItemRateLimiter(rate_percentage=40, **idle_gen_conf))

    # Apply Reset Sequence
    await tb.reset()

    # Enable random backpressure on the TX AXIS interface
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # Get dynamically resolved MVB item width
    data_width = tb.stream_in.item_widths["data"]
    meta_width = tb.stream_in.item_widths["meta"]

    cocotb.log.info(f"Starting transaction generation loop for {pkt_count} items...")

    # Generate random MVB data items
    for transaction_val in random_integers(0, 2**data_width - 1, pkt_count):
        random_mvb_transaction = random.randint(0, 2**meta_width - 1)
        mvb_tr = MvbTrClassicWithMeta()
        mvb_tr.data = transaction_val
        mvb_tr.meta = random_mvb_transaction

        # Pass transaction to the prediction model
        tb.model(mvb_tr)

        # Queue transaction into the driver
        tb.stream_in.append(mvb_tr)

    # Monitor progression loop
    last_num = 0
    while tb.stream_out.frame_cnt < pkt_count:
        if (tb.stream_out.frame_cnt // 1000) > last_num:
            last_num = tb.stream_out.frame_cnt // 1000
            cocotb.log.info(f"Progress: {tb.stream_out.frame_cnt}/{pkt_count} AXIS frames processed.")

        await ClockCycles(dut.CLK, 100)

    cocotb.log.info("All transactions processed successfully. Evaluating scoreboard results...")

    # Assert final verification results
    raise tb.scoreboard.result
