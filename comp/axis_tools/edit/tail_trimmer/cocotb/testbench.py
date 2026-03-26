# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_TAIL_TRIMMER component.

The trim instruction (TRIM_LENGTH and TRIM_ENABLE) is sampled only
during the FIRST word of each packet. For remaining words, these
signals are ignored.

The trim_length specifies the new desired packet length. If the packet
is longer than trim_length, excess bytes from the END (tail) are removed.
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotb_bus.scoreboard import Scoreboard
from dataclasses import dataclass
from typing import List


@dataclass
class TrimInstruction:
    """Trim instruction for a packet."""
    trim_length: int = 0
    trim_enable: int = 0


@dataclass
class Axi4StreamTransactionWithTrim(Axi4StreamTransaction):
    """Axi4Stream transaction with trim instruction signals."""
    TRIM_LENGTH: int = 0
    TRIM_ENABLE: int = 0


class Axi4StreamMasterWithTrim(Axi4StreamMaster):
    """Axi4StreamMaster with support for TRIM_LENGTH and TRIM_ENABLE signals."""
    _optional_signals = ["TLAST", "TKEEP", "TRIM_LENGTH", "TRIM_ENABLE"]


def _format_packet_bytes(packet_bytes: bytes, label: str) -> str:
    """Format packet bytes for display, 16 bytes per line."""
    lines = [f"{label}:"]
    for i in range(0, len(packet_bytes), 16):
        chunk = packet_bytes[i:i+16]
        hex_str = ' '.join(f'{b:02X}' for b in chunk)
        ascii_str = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
        lines.append(f"  {i:04X}: {hex_str:<48} {ascii_str}")
    return '\n'.join(lines)


def _compare_transactions(expected: Axi4StreamTransaction, actual: Axi4StreamTransaction,
                          packet_num: int = 0, trim_instr: TrimInstruction = None,
                          orig_len: int = 0) -> tuple:
    """Compare two AXI4-Stream transactions with detailed mismatch output."""
    match = expected.TDATA == actual.TDATA

    if match:
        return True, ""

    lines = []
    lines.append("")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#" + " " * 18 + f"PACKET MISMATCH #{packet_num}" + " " * 27 + "#")
    lines.append("#" + "=" * 64 + "#")
    if trim_instr:
        lines.append(f"#  Trim instruction: LENGTH={trim_instr.trim_length}, ENABLE={trim_instr.trim_enable}")
    lines.append(f"#  Original length: {orig_len:>5} bytes")
    lines.append("#" + "-" * 64 + "#")
    lines.append(f"#  Expected length: {len(expected.TDATA):>5} bytes")
    lines.append(f"#  Actual length:   {len(actual.TDATA):>5} bytes")
    lines.append("#" + "=" * 64 + "#")
    lines.append("")

    msg = "\n".join(lines)

    if hasattr(expected, 'TDATA') and expected.TDATA:
        msg += "\n" + _format_packet_bytes(expected.TDATA, "Expected output bytes") + "\n"
    if hasattr(actual, 'TDATA') and actual.TDATA:
        msg += "\n" + _format_packet_bytes(actual.TDATA, "Actual output bytes") + "\n"

    return False, msg


class Testbench:
    """Testbench for AXIS_TAIL_TRIMMER component."""

    def __init__(self, dut, debug: bool = False):
        self.dut = dut
        self.pkt_mtu = int(dut.PKT_MTU.value) if hasattr(dut, 'PKT_MTU') else 9216

        self.rx_driver = Axi4StreamMasterWithTrim(dut, "RX_AXI", dut.CLK)
        self.tx_monitor = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.pkts_sent = 0
        self.expected_output: List[Axi4StreamTransaction] = []
        self.packet_bytes_map: dict = {}
        self.trim_instr_map: dict = {}

        self.scoreboard = Scoreboard(dut)

        def compare_wrapper(actual):
            """Compare actual output with expected, providing detailed mismatch info."""
            if not self.expected_output:
                cocotb.log.error("Received unexpected packet")
                return
            expected = self.expected_output.pop(0)
            packet_num = self.pkts_sent - len(self.expected_output)
            expected.packet_bytes = self.packet_bytes_map.get(packet_num - 1, b'')
            trim_instr = self.trim_instr_map.get(packet_num - 1)
            orig_len = len(expected.packet_bytes) if hasattr(expected, 'packet_bytes') else 0
            match, msg = _compare_transactions(expected, actual, packet_num, trim_instr, orig_len)
            if not match:
                cocotb.log.error(f"Packet mismatch: {msg}")
                self.scoreboard.errors += 1
                raise AssertionError(f"Packet mismatch detected:\n{msg}")
            return match

        self.scoreboard.add_interface(self.tx_monitor, self.expected_output, compare_fn=compare_wrapper)

        if debug:
            self.rx_driver.log.setLevel(cocotb.logging.DEBUG)
            self.tx_monitor.log.setLevel(cocotb.logging.DEBUG)

    async def reset(self):
        self.dut.RESET.value = 1
        self.dut.TX_AXI_TREADY.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    def model(self, pkt_data: bytes, trim_instr: TrimInstruction) -> Axi4StreamTransaction:
        """Generate expected output by applying tail trim to packet data.

        If trim_enable is set and trim_length is less than packet length,
        the packet is truncated to trim_length bytes (removing bytes from the end).
        """
        if trim_instr.trim_enable and trim_instr.trim_length < len(pkt_data):
            # Trim from the end (tail) - keep only trim_length bytes from the start
            trimmed_data = pkt_data[:trim_instr.trim_length]
        else:
            # No trimming needed - packet is already short enough or trimming disabled
            trimmed_data = pkt_data

        expected_tr = Axi4StreamTransaction(TDATA=trimmed_data)
        expected_tr.packet_bytes = pkt_data
        self.expected_output.append(expected_tr)

        self.packet_bytes_map[self.pkts_sent] = pkt_data
        self.trim_instr_map[self.pkts_sent] = trim_instr

        self.pkts_sent += 1

        return expected_tr

    async def send_packet_with_trim(self, pkt_data: bytes, trim_instr: TrimInstruction):
        """Send packet via AXI-Stream with trim instruction.

        TRIM values are encoded for each word: first word has values, rest have zeros.
        """
        data_width = len(self.rx_driver.bus.TDATA) // 8
        word_cnt = (len(pkt_data) + data_width - 1) // data_width

        trim_len_width = len(self.rx_driver.bus.TRIM_LENGTH)
        trim_en_width = len(self.rx_driver.bus.TRIM_ENABLE)

        # Encode trim values for each word (same value on every word, like SEL in AXIS_SPLITTER)
        trim_len_encoded = 0
        trim_en_encoded = 0
        for i in range(word_cnt):
            word_trim_len = trim_instr.trim_length
            word_trim_en = trim_instr.trim_enable
            trim_len_encoded = (trim_len_encoded << trim_len_width) + word_trim_len
            trim_en_encoded = (trim_en_encoded << trim_en_width) + word_trim_en

        rx_tr = Axi4StreamTransactionWithTrim(
            TDATA=pkt_data,
            TRIM_LENGTH=trim_len_encoded,
            TRIM_ENABLE=trim_en_encoded
        )
        expected = self.model(pkt_data, trim_instr)

        cocotb.log.debug(f"Sending packet {self.pkts_sent}: len={len(pkt_data)}, words={word_cnt}, "
                         f"trim_len={trim_instr.trim_length}, trim_en={trim_instr.trim_enable}, "
                         f"expected_out_len={len(expected.TDATA)}")

        self.rx_driver.append(rx_tr)
