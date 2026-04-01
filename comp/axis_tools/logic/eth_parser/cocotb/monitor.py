# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Monitor module for AXIS_ETH_PARSER verification.

This module contains the HeadersMonitor class for capturing
extracted header information from the DUT.
"""

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_bus.monitors import BusMonitor

from scoreboard import AxisEthParserResult


class HeadersMonitor(BusMonitor):
    """Monitor for extracted headers from AXIS_ETH_PARSER.

    Monitors the HEADERS, HEADERS_VLD, and HEADERS_READY signals
    and captures extracted header information for scoreboard comparison.

    This class inherits from BusMonitor to be compatible with
    cocotb_bus.scoreboard.

    Attributes:
        dut: The Device Under Test (cocotb handle).
        clock: Clock signal for timing.
        captured_headers: List of captured AxisEthParserResult objects.
        item_cnt: Counter of captured header sets.
    """

    _signals = ["HEADERS_VLD", "HEADERS_READY"]

    def __init__(self, dut, clock, **kwargs):
        """Initialize the HeadersMonitor.

        Args:
            dut: Device Under Test handle
            clock: Clock signal for timing reference
        """
        # Initialize BusMonitor - pass None for callback since we override _monitor_recv
        super().__init__(dut, None, clock, **kwargs)

        self.dut = dut
        self.clock = clock
        self.captured_headers: List[AxisEthParserResult] = []
        self.item_cnt = 0

    async def _monitor_recv(self):
        """Monitor HEADERS_VLD and HEADERS_READY to capture header values.

        This method is called by the BusMonitor base class to capture
        header values whenever a valid handshake occurs (HEADERS_VLD=1
        and HEADERS_READY=1).

        This coroutine runs indefinitely, capturing header values
        only when both valid and ready are asserted (handshake).
        Callbacks are invoked for each captured header set before storing.
        """
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            if self.in_reset:
                continue

            # Capture only on valid handshake (VLD and READY both asserted)
            if self.dut.HEADERS_VLD.value == 1 and self.dut.HEADERS_READY.value == 1:
                headers = self._capture_headers()
                self._recv(headers)
                self.item_cnt += 1
                cocotb.log.debug(
                    f"Captured headers #{self.item_cnt}: "
                    f"eth_vld={headers.eth_vld}, "
                    f"ipv4_vld={headers.ipv4_vld}, "
                    f"tcp_vld={headers.tcp_vld}, "
                    f"udp_vld={headers.udp_vld}"
                )

    def _capture_headers(self) -> AxisEthParserResult:
        """Capture current header values from DUT signals.

        Reads all header field signals from the DUT and returns
        them as an AxisEthParserResult object.

        Returns:
            AxisEthParserResult: Captured header values
        """
        result = AxisEthParserResult()
        result.packet_num = self.item_cnt

        # Ethernet header
        result.eth_dst_mac = int(self.dut.HEADERS.eth.dst_mac.value)
        result.eth_src_mac = int(self.dut.HEADERS.eth.src_mac.value)
        result.eth_ethertype = int(self.dut.HEADERS.eth.ethertype.value)
        result.eth_vld = int(self.dut.HEADERS.eth_vld.value)
        result.eth_offset = int(self.dut.HEADERS.eth_offset.value)

        # VLAN header
        result.vlan_tci = int(self.dut.HEADERS.vlan.tci.value)
        result.vlan_ethertype = int(self.dut.HEADERS.vlan.ethertype.value)
        result.vlan_vld = int(self.dut.HEADERS.vlan_vld.value)
        result.vlan_offset = int(self.dut.HEADERS.vlan_offset.value)

        # IPv4 header
        result.ipv4_version = int(self.dut.HEADERS.ipv4.version.value)
        result.ipv4_ihl = int(self.dut.HEADERS.ipv4.ihl.value)
        result.ipv4_tos = int(self.dut.HEADERS.ipv4.tos.value)
        result.ipv4_total_length = int(self.dut.HEADERS.ipv4.total_length.value)
        result.ipv4_identification = int(self.dut.HEADERS.ipv4.identification.value)
        result.ipv4_flags = int(self.dut.HEADERS.ipv4.flags.value)
        result.ipv4_fragment_offset = int(self.dut.HEADERS.ipv4.fragment_offset.value)
        result.ipv4_ttl = int(self.dut.HEADERS.ipv4.ttl.value)
        result.ipv4_protocol = int(self.dut.HEADERS.ipv4.protocol.value)
        result.ipv4_header_checksum = int(self.dut.HEADERS.ipv4.header_checksum.value)
        result.ipv4_src_ip = int(self.dut.HEADERS.ipv4.src_ip.value)
        result.ipv4_dst_ip = int(self.dut.HEADERS.ipv4.dst_ip.value)
        result.ipv4_vld = int(self.dut.HEADERS.ipv4_vld.value)
        result.ipv4_offset = int(self.dut.HEADERS.ipv4_offset.value)

        # TCP header
        result.tcp_src_port = int(self.dut.HEADERS.tcp.src_port.value)
        result.tcp_dst_port = int(self.dut.HEADERS.tcp.dst_port.value)
        result.tcp_seq_num = int(self.dut.HEADERS.tcp.seq_num.value)
        result.tcp_ack_num = int(self.dut.HEADERS.tcp.ack_num.value)
        result.tcp_data_offset = int(self.dut.HEADERS.tcp.data_offset.value)
        result.tcp_reserved = int(self.dut.HEADERS.tcp.reserved.value)
        result.tcp_flags = int(self.dut.HEADERS.tcp.flags.value)
        result.tcp_window = int(self.dut.HEADERS.tcp.window.value)
        result.tcp_checksum = int(self.dut.HEADERS.tcp.checksum.value)
        result.tcp_urgent_ptr = int(self.dut.HEADERS.tcp.urgent_ptr.value)
        result.tcp_vld = int(self.dut.HEADERS.tcp_vld.value)
        result.tcp_offset = int(self.dut.HEADERS.tcp_offset.value)

        # UDP header
        result.udp_src_port = int(self.dut.HEADERS.udp.src_port.value)
        result.udp_dst_port = int(self.dut.HEADERS.udp.dst_port.value)
        result.udp_length = int(self.dut.HEADERS.udp.length.value)
        result.udp_checksum = int(self.dut.HEADERS.udp.checksum.value)
        result.udp_vld = int(self.dut.HEADERS.udp_vld.value)
        result.udp_offset = int(self.dut.HEADERS.udp_offset.value)

        return result
