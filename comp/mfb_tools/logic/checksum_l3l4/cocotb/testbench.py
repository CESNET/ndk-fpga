# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import ipaddress
import cocotb
import logging
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.base.types import LogicArray
from cocotbext.ofm.base.protocol import optional_signal, alias
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mfb.transaction import MfbTransaction
from cocotbext.ofm.mvb.transaction import MvbTransaction
from cocotbext.ofm.mvb.protocol import MvbProtocol
from cocotb_bus.drivers import BitDriver
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMvbInterface
from dataclasses import dataclass
from scapy.all import raw, TCP, UDP, SCTP, ICMPv6EchoRequest

from cocotbext.ofm.utils.scapy import ScapyPacketGenerator
from scoreboard import MfbChecksumL3L4Result, compare_checksums


@dataclass
class MetadataTr(MvbTransaction):
    """MVB transaction for L3/L4 metadata"""
    l3_csum_orig: int = 0
    l3_csum_en: int = 0
    l3_offset: int = 0
    l3_length: int = 0
    l4_csum_orig: int = 0
    l4_csum_en: int = 0
    l4_offset: int = 0
    l4_length: int = 0
    l4_protocol: int = 0
    ip_src_addr: int = 0
    ip_dst_addr: int = 0
    ip_ver6: int = 0
    pkt_length: int = 0


@dataclass
class MvbTxResult(MvbTransaction):
    """MVB transaction for TX checksum results"""
    l3_csum: int = 0
    l3_csum_ok: int = 0
    l3_csum_en: int = 0
    l4_csum: int = 0
    l4_csum_ok: int = 0
    l4_csum_en: int = 0


class MfbChecksumL3L4MvbProtocol(MvbProtocol):
    mfb_regions  : int = alias(MvbProtocol.items)

    l3_csum_en   : LogicArray = optional_signal(put_with="vld")
    l3_csum_orig : LogicArray = optional_signal(put_with="l3_csum_en")
    l3_offset    : LogicArray = optional_signal(put_with="l3_csum_en")
    l3_length    : LogicArray = optional_signal(put_with="l3_csum_en")

    l4_csum_en   : LogicArray = optional_signal(put_with="vld")
    l4_csum_orig : LogicArray = optional_signal(put_with="l4_csum_en")
    l4_offset    : LogicArray = optional_signal(put_with="l4_csum_en")
    l4_length    : LogicArray = optional_signal(put_with="l4_csum_en")
    l4_protocol  : LogicArray = optional_signal(put_with="l4_csum_en")

    ip_src_addr  : LogicArray = optional_signal(put_with="vld")
    ip_dst_addr  : LogicArray = optional_signal(put_with="vld")
    ip_ver6      : LogicArray = optional_signal(put_with="vld")
    pkt_length   : LogicArray = optional_signal(put_with="vld")


class MVBMonitorExt(MVBMonitor):
    _optional_signals = [
        "l3_csum", "l3_csum_ok", "l3_csum_en",
        "l4_csum", "l4_csum_ok", "l4_csum_en",
        "vld"
    ]


class Testbench:
    """Testbench for MFB_CHECKSUM_L3L4 component.

    This class provides a complete testbench environment for testing the
    MFB_CHECKSUM_L3L4 VHDL component. It includes MFB and MVB drivers for
    sending packets and metadata, an MVB monitor for receiving results,
    a scoreboard for verification, and a throughput probe for performance
    measurement.

    Attributes:
        dut: The Device Under Test (cocotb handle).
        mfb_driver: MFBDriver for sending packet data.
        mvb_driver: MVBDriver for sending L3/L4 metadata.
        mvb_tx_monitor: MVBMonitorExt for receiving checksum results.
        backpressure: BitDriver for controlling TX backpressure.
        scoreboard: Scoreboard for comparing expected vs actual results.
        throughput_probe: ThroughputProbe for performance measurement.
        pkts_sent: Counter of sent packets.
        expected_output: List of expected MvbTxResult transactions.
    """

    def __init__(self, dut, debug=False, log_comparisons=True):
        self.dut = dut

        # MFB driver for packet data
        self.mfb_driver = MFBDriver(dut, "RX_MFB", dut.CLK, generics_prefix="MFB", rate_limiter_config=dict(max_idles=5, zero_idles_chance=50))

        # MVB driver for combined L3 and L4 metadata
        self.mvb_driver = MVBDriver(dut, "RX_MVB", dut.CLK, protocol=MfbChecksumL3L4MvbProtocol, rate_limiter_config=dict(max_idles=5, zero_idles_chance=50))

        # MVB monitor for TX results
        self.mvb_tx_monitor = MVBMonitorExt(dut, "TX_MVB", dut.CLK, tr_type=MvbTxResult)
        # Add callback to zero out csum values when en is zero
        self.mvb_tx_monitor.add_callback(self._process_tx_transaction)

        # Backpressure driver for TX MVB
        self.backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)

        # Counter of sent transactions
        self.pkts_sent = 0

        # List of expected results for scoreboard
        self.expected_output = []

        # Setting up custom scoreboard which compares received transactions with expected transactions
        # using the nice comparison format from AXI-Stream Ethernet Parser verification
        self.scoreboard = None  # Custom scoreboard implemented via monitor callback
        self.scoreboard_errors = []
        self.scoreboard_comparisons = 0
        self.stop_on_error = True  # Stop test on first scoreboard error
        self.log_comparisons = log_comparisons  # Enable/disable scoreboard error logging

        # Add callback for scoreboard comparison
        self.mvb_tx_monitor.add_callback(self._scoreboard_compare)

        # Setting up throughput probe for performance measurement
        self.throughput_probe = ThroughputProbe(
            ThroughputProbeMvbInterface(self.mvb_tx_monitor),
            throughput_units="items"
        )
        self.throughput_probe.add_log_interval(0, None)
        self.throughput_probe.set_log_period(20)

        # Setting up logging level
        if debug:
            self.mfb_driver.log.setLevel(logging.DEBUG)
            self.mvb_driver.log.setLevel(logging.DEBUG)
            self.mvb_tx_monitor.log.setLevel(logging.DEBUG)

    def _process_tx_transaction(self, transaction):
        """Process TX transaction: zero out csum values and ok flags when en is zero.

        This callback is registered with the MVB TX monitor to normalize received
        transactions before scoreboard comparison. When checksum is disabled (en=0),
        the DUT outputs zeros for checksum value and ok flag.

        Args:
            transaction: The MvbTxResult transaction received from the monitor.
        """
        if transaction.l3_csum_en == 0:
            transaction.l3_csum = 0
            transaction.l3_csum_ok = 0
        if transaction.l4_csum_en == 0:
            transaction.l4_csum = 0
            transaction.l4_csum_ok = 0

    async def reset(self):
        """Perform a hardware reset sequence.

        Drives the RESET signal high for 8 clock cycles, then releases it.
        Waits for one rising edge after reset release.
        """
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    def model(self, pkt_dict):
        """Generate expected output transaction based on input packet.

        This is the reference model that predicts the DUT's output based on
        the input packet metadata. It creates an MfbChecksumL3L4Result transaction with
        expected checksum values and flags.

        Args:
            pkt_dict: Dictionary containing packet metadata including checksum
                     information (see generate_packet_for_test return value).

        Returns:
            MfbChecksumL3L4Result: The expected output transaction.
        """
        # Create expected output result based on input packet
        expected_result = MfbChecksumL3L4Result(
            l3_csum=pkt_dict["l3_csum_orig"] if pkt_dict["ipv6_vld"] == 0 else 0,
            l3_csum_ok=1 if pkt_dict["l3_csum_en"] else 0,
            l3_csum_en=pkt_dict["l3_csum_en"],
            l4_csum=pkt_dict["l4_csum_orig"],
            l4_csum_ok=1 if pkt_dict["l4_csum_en"] else 0,
            l4_csum_en=pkt_dict["l4_csum_en"],
            packet_num=self.pkts_sent + 1,
            packet_bytes=pkt_dict.get("packet_bytes", b'')
        )

        self.expected_output.append(expected_result)
        self.pkts_sent += 1

        return expected_result

    def _scoreboard_compare(self, actual_tr):
        """Custom scoreboard comparison callback with formatted output.

        This callback compares expected vs actual checksum results and logs
        detailed comparison tables on mismatch. Stops test on first error
        if stop_on_error is True.

        Args:
            actual_tr: The actual MvbTxResult transaction from the DUT.
        """
        if not self.expected_output:
            cocotb.log.warning("No expected output available for comparison")
            return

        # Get next expected result
        expected = self.expected_output.pop(0)

        # Convert actual transaction to result object for comparison
        actual = MfbChecksumL3L4Result(
            l3_csum=actual_tr.l3_csum,
            l3_csum_ok=actual_tr.l3_csum_ok,
            l3_csum_en=actual_tr.l3_csum_en,
            l4_csum=actual_tr.l4_csum,
            l4_csum_ok=actual_tr.l4_csum_ok,
            l4_csum_en=actual_tr.l4_csum_en,
            packet_num=expected.packet_num,
            packet_bytes=expected.packet_bytes
        )

        self.scoreboard_comparisons += 1

        # Compare using the formatted comparison function
        match, msg = compare_checksums(expected, actual)

        if not match:
            self.scoreboard_errors.append(msg)
            if self.log_comparisons:
                cocotb.log.error(f"Scoreboard mismatch at transaction {self.scoreboard_comparisons}")
                cocotb.log.error(msg)

            # Stop test on first error if enabled
            if self.stop_on_error:
                raise AssertionError(f"Scoreboard mismatch at transaction {self.scoreboard_comparisons}")

    async def send_packet_with_metadata(self, pkt_dict):
        """Send packet via MFB and metadata via MVB bus.

        Creates MFB and MVB transactions from the packet dictionary and
        appends them to the respective drivers. Also generates the expected
        output via the model and adds it to the scoreboard.

        Args:
            pkt_dict: Dictionary containing packet data and metadata
                     (see generate_packet_for_test return value).
        """
        packet_bytes = pkt_dict["packet_bytes"]

        # Create MFB transaction
        mfb_tr = MfbTransaction(data=packet_bytes)

        # Create combined metadata transaction
        meta = MetadataTr(
            l3_csum_orig=pkt_dict["l3_csum_orig"],
            l3_csum_en=pkt_dict["l3_csum_en"],
            l3_offset=pkt_dict["l3_offset"],
            l3_length=pkt_dict["l3_length"],
            l4_csum_orig=pkt_dict["l4_csum_orig"],
            l4_csum_en=pkt_dict["l4_csum_en"],
            l4_offset=pkt_dict["l4_offset"],
            l4_length=pkt_dict["l4_length"],
            l4_protocol=pkt_dict["l4_proto_number"],
            ip_src_addr=pkt_dict["src_ip_128b"],
            ip_dst_addr=pkt_dict["dst_ip_128b"],
            ip_ver6=pkt_dict["ipv6_vld"],
            pkt_length=pkt_dict["packet_length"]
        )

        # Add expected output to scoreboard via model
        self.model(pkt_dict)

        # Send transactions
        self.mfb_driver.append(mfb_tr)
        self.mvb_driver.append(meta)

        cocotb.log.debug(f"Sent packet {self.pkts_sent}: L3_offset={pkt_dict['l3_offset']}, "
                         f"L4_offset={pkt_dict['l4_offset']}, IPv6={pkt_dict['ipv6_vld']}")

    @staticmethod
    def ip_to_128b(ip_str: str) -> int:
        """Convert IP address string to 128-bit integer.

        Converts IPv4 or IPv6 address strings to 128-bit integers.
        IPv4 addresses are converted to IPv4-mapped IPv6 format
        (::ffff:0:0/96 prefix followed by the 32-bit IPv4 address).

        Args:
            ip_str: IP address string (e.g., "192.168.1.1" or "2001:db8::1").

        Returns:
            int: 128-bit integer representation of the IP address.
        """
        ip = ipaddress.ip_address(ip_str)
        if ip.version == 4:
            # IPv4-mapped IPv6: 0:96 bits = 0x00000000000000000000FFFF
            return (0x00000000000000000000FFFF << 32) | int(ip)
        else:
            return int(ip)

    async def generate_and_send_packet(self, min_len: int = 60, max_len: int = 1518, truncate_chance: float = 0.0) -> dict:
        """Generate a packet and send it via MFB/MVB buses.

        Convenience method that combines generate_packet_for_test() and
        send_packet_with_metadata() into a single call.

        Args:
            min_len: Minimum packet length in bytes (default: 60).
            max_len: Maximum packet length in bytes (default: 1518).
            truncate_chance: Probability of truncating the packet (0.0-1.0, default: 0.0).

        Returns:
            dict: Dictionary with packet data and metadata for debugging.
        """
        pkt_dict = self.generate_packet_for_test(min_len, max_len, truncate_chance)
        await self.send_packet_with_metadata(pkt_dict)
        return pkt_dict

    def generate_packet_for_test(self, min_len: int = 60, max_len: int = 1518, truncate_chance: float = 0.0) -> dict:
        """Generate packet and convert to format required by checksum_l3l4 test.

        This method uses ScapyPacketGenerator class to generate a packet and extract
        metadata, then converts it to the dictionary format expected by the testbench.
        Optionally truncates the packet to simulate corrupted/damaged packets.

        Args:
            min_len: Minimum packet length in bytes (default: 60).
            max_len: Maximum packet length in bytes (default: 1518).
            truncate_chance: Probability of truncating the packet (0.0-1.0, default: 0.0).

        Returns:
            dict: Dictionary with packet data and metadata in test-specific format.
        """
        import random

        pkt = ScapyPacketGenerator.generate(min_len, max_len)
        packet_bytes = bytearray(raw(pkt))

        # Optionally truncate the packet to simulate damaged packets
        if truncate_chance > 0 and random.random() < truncate_chance:
            # Calculate truncation parameters
            original_len = len(packet_bytes)
            # Ensure we keep at least min_len bytes (default 60)
            # Truncate significantly: keep between min_len and 75% of original length
            max_keep = max(min_len, int(original_len * 0.75))
            if max_keep > min_len:
                new_len = random.randint(min_len, max_keep)
            else:
                new_len = min_len

            # Truncate the packet bytes
            packet_bytes = packet_bytes[:new_len]

            cocotb.log.debug(f"Truncated packet from {original_len} to {new_len} bytes")

        # Get L3 info (includes offset)
        l3_offset, l3_length, l3_proto_number, l3_csum_en, l3_checksum = ScapyPacketGenerator.get_l3_info(pkt)

        # Get L4 info (includes offset, needs l3_length)
        l4_offset, l4_length, l4_proto_number, l4_csum_en, l4_checksum = ScapyPacketGenerator.get_l4_info(pkt, l3_length)

        # Get IP addresses (as strings only)
        src_ip, dst_ip = ScapyPacketGenerator.get_ip_addresses(pkt)

        # Convert to 128-bit integers (test-specific)
        src_ip_128b = self.ip_to_128b(src_ip)
        dst_ip_128b = self.ip_to_128b(dst_ip)

        # ipv6_vld can be derived from l3_proto_number (6 = IPv6)
        ipv6_vld = 1 if l3_proto_number == 6 else 0

        # Extract L4 bytes
        if pkt.haslayer(TCP):
            l4_bytes = raw(pkt[TCP])
        elif pkt.haslayer(UDP):
            l4_bytes = raw(pkt[UDP])
        elif pkt.haslayer(SCTP):
            l4_bytes = raw(pkt[SCTP])
        elif pkt.haslayer(ICMPv6EchoRequest):
            l4_bytes = raw(pkt[ICMPv6EchoRequest])
        else:
            l4_bytes = b""

        return {
            "pkt": pkt,
            "packet_bytes": packet_bytes,
            "l3_checksum": l3_checksum,
            "l4_checksum": l4_checksum,
            "l3_offset": l3_offset,
            "l4_offset": l4_offset,
            "l3_length": l3_length,
            "l4_length": l4_length,
            "src_ip": src_ip,
            "dst_ip": dst_ip,
            "src_ip_128b": src_ip_128b,
            "dst_ip_128b": dst_ip_128b,
            "ipv6_vld": ipv6_vld,
            "ip_header_length": l3_length,
            "l4_proto_number": l4_proto_number,
            "l3_csum_orig": l3_checksum if l3_checksum is not None else 0,
            "l3_csum_en": l3_csum_en,
            "l4_csum_orig": l4_checksum,
            "l4_csum_en": l4_csum_en,
            "l4_bytes": l4_bytes,
            "packet_length": len(packet_bytes)
        }
