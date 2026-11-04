# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_ETH_PARSER component.

This class provides a complete testbench environment for testing the
AXIS_ETH_PARSER VHDL component. It includes AXI4-Stream drivers for
sending and receiving packets, a scoreboard for verification, and
uses scapy for packet generation.

Supported protocol stack:
    - Ethernet + [VLAN] + [IPv4] + [TCP/UDP]
"""

import random
from typing import List

import cocotb
import logging
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster, Axi4StreamSlave
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotb_bus.scoreboard import Scoreboard
from scapy.all import IP, raw

from cocotbext.ofm.utils.scapy import ScapyPacketGenerator
from scoreboard import AxisEthParserResult, compare_headers as _compare_headers
from monitor import HeadersMonitor
from model import AxisEthParserModel


class Testbench:
    """Testbench for AXIS_ETH_PARSER component.

    This class provides a complete testbench environment for testing the
    AXIS_ETH_PARSER VHDL component. It includes AXI4-Stream drivers for
    sending and receiving packets, a headers monitor for capturing
    extracted header information, and a scoreboard for verification.

    Attributes:
        dut: The Device Under Test (cocotb handle).
        rx_driver: Axi4StreamMaster for sending packet data.
        tx_driver: Axi4StreamSlave for receiving packet data.
        headers_monitor: HeadersMonitor for capturing extracted headers.
        scoreboard: Scoreboard for comparing expected vs actual results.
        pkts_sent: Counter of sent packets.
        expected_output: List of expected AxisEthParserResult objects.
    """

    def __init__(self, dut, debug=False, rate_limiter_config: dict = {}):
        """Initialize the testbench.

        Args:
            dut: Device Under Test handle
            debug: Enable debug logging (default: False)
            rate_limiter_config: Configuration for the RX driver's ItemRateLimiter
        """
        self.dut = dut

        # Verbose mode
        self.verbose = False

        # RX AXI4-Stream master driver
        self.rx_driver = Axi4StreamMaster(dut, "RX_AXI", dut.CLK, rate_limiter_config=rate_limiter_config)

        # TX AXI4-Stream slave driver (for backpressure control)
        self.tx_driver = Axi4StreamSlave(dut, "TX_AXI", dut.CLK)

        # Headers monitor
        self.headers_monitor = HeadersMonitor(dut, dut.CLK)

        # Reference model
        self.model = AxisEthParserModel()

        # Counter of sent transactions
        self.pkts_sent = 0

        # List of expected results for scoreboard
        self.expected_output: List[AxisEthParserResult] = []

        # Dictionary to store packet bytes by packet number for DUT output
        self.packet_bytes_map: dict = {}

        # Setting up scoreboard which compares received transactions with expected transactions
        self.scoreboard = Scoreboard(dut)

        # Create a wrapper function for comparison that handles the expected/actual comparison
        def compare_wrapper(actual):
            """Wrapper for compare_headers that pops expected and compares with actual.

            Stops the test on first error by raising AssertionError.
            """
            if not self.expected_output:
                cocotb.log.error("Received unexpected header")
                return
            expected = self.expected_output.pop(0)
            # Assign packet bytes to actual result for display
            actual.packet_bytes = self.packet_bytes_map.get(expected.packet_num, b'')
            match, msg = _compare_headers(expected, actual)
            if not match:
                cocotb.log.error(f"Header mismatch: {msg}")
                self.scoreboard.errors += 1
                # Stop on first error
                raise AssertionError(f"Header mismatch detected:\n{msg}")
            elif self.verbose:
                cocotb.log.info(f"Header match: {msg}")
            return match

        # Linking monitor with its expected output
        self.scoreboard.add_interface(self.headers_monitor, self.expected_output,
                                      compare_fn=compare_wrapper)

        # Setting up logging level
        if debug:
            self.rx_driver.log.setLevel(logging.DEBUG)

    async def reset(self):
        """Perform a hardware reset sequence.

        Drives the RESET signal high for 8 clock cycles, then releases it.
        Waits for one rising edge after reset release.
        Also initializes HEADERS_READY to 1 (ready to accept).
        """
        # Initialize HEADERS_READY to 1 (ready state)
        self.dut.HEADERS_READY.value = 1

        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    def generate_expected(self, pkt, packet_bytes: bytes = None) -> AxisEthParserResult:
        """Generate expected output using the reference model.

        Args:
            pkt: Scapy packet object.
            packet_bytes: Raw packet bytes for debugging.

        Returns:
            AxisEthParserResult: The expected output transaction.
        """
        expected = self.model.extract_headers(pkt, packet_bytes)
        expected.packet_num = self.pkts_sent
        self.expected_output.append(expected)
        self.pkts_sent += 1
        return expected

    @staticmethod
    def malform_ipv4(pkt, packet_bytes: bytes, min_len: int) -> bytes:
        """Set a random IHL and protocol in the IPv4 header and cut the packet short.

        The packet then announces headers that end after the last byte of the
        packet. The length stays at least min_len, so the packet looks like
        a padded minimum-size frame on a real link.

        Args:
            pkt: Scapy packet that packet_bytes was built from.
            packet_bytes: Raw packet bytes.
            min_len: Minimum packet length after the cut.

        Returns:
            bytes: Changed packet bytes, or the original bytes when the packet has no IPv4.
        """
        if IP not in pkt:
            return packet_bytes

        l3_offset = len(packet_bytes) - len(raw(pkt[IP]))
        ihl = random.randint(5, 15)
        data = bytearray(packet_bytes)
        data[l3_offset] = 0x40 | ihl
        data[l3_offset + 9] = random.choice([6, 17, 1])

        max_cut_len = max(min_len, min(len(data), l3_offset + ihl * 4 + 28))
        new_len = random.randint(min_len, max_cut_len)
        return bytes(data[:new_len])

    async def generate_and_send_packet(
        self,
        min_len: int = 60,
        max_len: int = 1518,
        corrupt_prob: float = 0.0,
        malform_prob: float = 0.0
    ) -> dict:
        """Generate and send packet via AXI4-Stream. Optionally corrupt by truncation.

        Args:
            min_len: Min packet length (default: 60). Also used as min length after corruption.
            max_len: Max packet length (default: 1518).
            corrupt_prob: Corruption probability 0.0-1.0 (default: 0.0 = no corruption).
            malform_prob: Probability 0.0-1.0 of a malformed IPv4 header (see malform_ipv4).

        Returns:
            dict: Packet info {pkt, packet_bytes, len}.
        """
        pkt = ScapyPacketGenerator.generate(min_len, max_len)
        packet_bytes = raw(pkt)

        # Corrupt packet by truncation with given probability
        if corrupt_prob > 0 and random.random() < corrupt_prob:
            orig_len = len(packet_bytes)
            if orig_len > min_len:
                new_len = random.randint(min_len, orig_len - 1)
                packet_bytes = packet_bytes[:new_len]
                cocotb.log.debug(f"Packet corrupted: {orig_len} -> {new_len} bytes")

        if malform_prob > 0 and random.random() < malform_prob:
            packet_bytes = self.malform_ipv4(pkt, packet_bytes, min_len)

        axi_tr = Axi4StreamTransaction(TDATA=packet_bytes)
        expected = self.generate_expected(pkt, packet_bytes)
        self.packet_bytes_map[expected.packet_num] = packet_bytes
        self.rx_driver.append(axi_tr)

        cocotb.log.debug(f"Sent packet {self.pkts_sent}: {len(packet_bytes)} bytes")
        return {"pkt": pkt, "packet_bytes": packet_bytes, "len": len(packet_bytes)}
