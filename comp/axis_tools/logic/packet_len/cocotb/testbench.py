# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): David Vodak <vodak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_PACKET_LEN component.

This component counts the length of each AXI-Stream packet in bytes.
The packet length is output on the TX_PACKET_LEN port and is valid
together with the TX_AXI_TLAST signal.

The component has a 1-cycle latency (registered output) and passes
AXI-Stream data through unchanged.
"""

import cocotb
import logging
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotb_bus.scoreboard import Scoreboard
from typing import List


class Testbench:
    """Testbench for AXIS_PACKET_LEN component.

    Verifies two properties:
    1. AXI-Stream data passes through unchanged (passthrough check).
    2. TX_PACKET_LEN reports the correct byte count for each packet,
       valid together with TX_AXI_TLAST.

    Attributes:
        dut: The Device Under Test (cocotb handle).
        rx_driver: Axi4StreamMaster for sending packet data.
        tx_monitor: Axi4Stream monitor for capturing output packets.
        scoreboard: Scoreboard for data passthrough verification.
        pkts_sent: Counter of sent packets.
        expected_output: List of expected Axi4StreamTransaction objects.
        expected_lengths: Queue of expected packet lengths in bytes.
        length_errors: Counter of packet length mismatches.
    """

    def __init__(self, dut, debug: bool = False):
        self.dut = dut

        # RX AXI4-Stream master driver
        self.rx_driver = Axi4StreamMaster(dut, "RX_AXI", dut.CLK)

        # TX AXI4-Stream monitor
        self.tx_monitor = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        # Counter of sent transactions
        self.pkts_sent = 0

        # Expected output for data passthrough scoreboard
        self.expected_output: List[Axi4StreamTransaction] = []

        # Expected packet lengths for TX_PACKET_LEN verification
        self.expected_lengths: List[int] = []

        # Packet length error counter
        self.length_errors = 0

        # Scoreboard for data passthrough verification
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.tx_monitor, self.expected_output)

        # Start the packet length monitor coroutine
        self._len_monitor_task = cocotb.start_soon(self._monitor_packet_len())

        if debug:
            self.rx_driver.log.setLevel(logging.DEBUG)
            self.tx_monitor.log.setLevel(logging.DEBUG)

    async def reset(self):
        """Perform a hardware reset sequence.

        Drives the RESET signal high for 8 clock cycles, then releases it.
        Waits for one rising edge after reset release.
        Also initializes TX_AXI_TREADY to 1 (ready to accept).
        """
        self.dut.TX_AXI_TREADY.value = 1
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def _monitor_packet_len(self):
        """Monitor TX_PACKET_LEN when TX_AXI_TLAST is asserted.

        On each clock edge, checks if a valid transfer with TLAST is
        occurring on the TX interface. If so, captures TX_PACKET_LEN
        and compares it with the next expected packet length.
        """
        re = RisingEdge(self.dut.CLK)
        while True:
            await re
            tvalid = int(self.dut.TX_AXI_TVALID.value)
            tready = int(self.dut.TX_AXI_TREADY.value)
            tlast = int(self.dut.TX_AXI_TLAST.value)

            if tvalid and tready and tlast:
                actual_len = int(self.dut.TX_PACKET_LEN.value)
                if self.expected_lengths:
                    expected_len = self.expected_lengths.pop(0)
                    pkt_num = self.pkts_sent - len(self.expected_lengths)
                    if actual_len != expected_len:
                        self.length_errors += 1
                        cocotb.log.error(
                            f"Packet length mismatch #{pkt_num}: "
                            f"expected {expected_len} bytes, got {actual_len} bytes"
                        )
                        raise AssertionError(
                            f"Packet length mismatch #{pkt_num}: "
                            f"expected {expected_len}, got {actual_len}"
                        )
                    else:
                        cocotb.log.debug(
                            f"Packet #{pkt_num} length OK: {actual_len} bytes"
                        )
                else:
                    self.length_errors += 1
                    cocotb.log.error(
                        f"Unexpected TX_PACKET_LEN output: {actual_len} "
                        f"(no expected length queued)"
                    )

    def model(self, pkt_data: bytes) -> Axi4StreamTransaction:
        """Generate expected output for passthrough verification and queue expected length.

        The component passes AXI-Stream data through unchanged, so the
        expected output is identical to the input. The expected packet
        length is simply the number of bytes in the packet.

        Args:
            pkt_data: Raw packet bytes.

        Returns:
            Axi4StreamTransaction: The expected output transaction.
        """
        expected_tr = Axi4StreamTransaction(TDATA=pkt_data)
        self.expected_output.append(expected_tr)
        self.expected_lengths.append(len(pkt_data))
        self.pkts_sent += 1
        return expected_tr

    async def send_packet(self, pkt_data: bytes):
        """Send a packet via AXI-Stream and register expected outputs.

        Args:
            pkt_data: Raw packet bytes to send.
        """
        self.model(pkt_data)
        rx_tr = Axi4StreamTransaction(TDATA=pkt_data)
        self.rx_driver.append(rx_tr)
