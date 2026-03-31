# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): David Vodak <vodak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_PACKET_EDITOR component."""

from dataclasses import dataclass
from typing import List

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction


@dataclass
class EditInstruction:
    """Edit instruction for one packet."""
    edit_data: bytes
    edit_offset: int = 0
    edit_mask: int = 0
    edit_enable: int = 0


@dataclass
class Axi4StreamTransactionWithEdit(Axi4StreamTransaction):
    """Axi4Stream transaction with edit instruction signals."""
    EDIT_DATA: int = 0
    EDIT_OFFSET: int = 0
    EDIT_MASK: int = 0
    EDIT_ENABLE: int = 0


class Axi4StreamMasterWithEdit(Axi4StreamMaster):
    """Axi4StreamMaster with support for packet edit instruction."""
    _optional_signals = ["TLAST", "TKEEP", "EDIT_DATA", "EDIT_OFFSET", "EDIT_MASK", "EDIT_ENABLE"]


def _format_packet_bytes(packet_bytes: bytes, label: str) -> str:
    """Format packet bytes for display, 16 bytes per line."""
    lines = [f"{label}:"]
    for i in range(0, len(packet_bytes), 16):
        chunk = packet_bytes[i:i+16]
        hex_str = " ".join(f"{b:02X}" for b in chunk)
        ascii_str = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
        lines.append(f"  {i:04X}: {hex_str:<48} {ascii_str}")
    return "\n".join(lines)


def _compare_transactions(expected: Axi4StreamTransaction, actual: Axi4StreamTransaction,
                          packet_num: int = 0, edit_instr: EditInstruction = None) -> tuple:
    """Compare two AXI4-Stream transactions with detailed mismatch output."""
    match = expected.TDATA == actual.TDATA

    if match:
        return True, ""

    lines = []
    lines.append("")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#" + " " * 17 + f"PACKET MISMATCH #{packet_num}" + " " * 27 + "#")
    lines.append("#" + "=" * 64 + "#")
    if edit_instr:
        lines.append(
            f"#  Edit instruction: OFFSET={edit_instr.edit_offset}, "
            f"MASK=0x{edit_instr.edit_mask:0X}, ENABLE={edit_instr.edit_enable}"
        )
    lines.append(f"#  Expected length: {len(expected.TDATA):>5} bytes")
    lines.append(f"#  Actual length:   {len(actual.TDATA):>5} bytes")
    lines.append("#" + "=" * 64 + "#")
    lines.append("")

    msg = "\n".join(lines)
    if hasattr(expected, "TDATA") and expected.TDATA:
        msg += "\n" + _format_packet_bytes(expected.TDATA, "Expected output bytes") + "\n"
    if hasattr(actual, "TDATA") and actual.TDATA:
        msg += "\n" + _format_packet_bytes(actual.TDATA, "Actual output bytes") + "\n"

    return False, msg


class Testbench:
    """Testbench for AXIS_PACKET_EDITOR component."""

    def __init__(self, dut, debug: bool = False):
        self.dut = dut

        self.rx_driver = Axi4StreamMasterWithEdit(dut, "RX_AXI", dut.CLK)
        self.tx_monitor = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.edit_bytes = int(dut.EDIT_BYTES.value) if hasattr(dut, "EDIT_BYTES") else 16

        self.pkts_sent = 0
        self.expected_output: List[Axi4StreamTransaction] = []
        self.edit_instr_map: dict = {}

        self.scoreboard = Scoreboard(dut)

        def compare_wrapper(actual):
            """Compare actual output with expected, providing detailed mismatch info."""
            if not self.expected_output:
                cocotb.log.error("Received unexpected packet")
                return
            expected = self.expected_output.pop(0)
            packet_num = self.pkts_sent - len(self.expected_output)
            edit_instr = self.edit_instr_map.get(packet_num - 1)
            match, msg = _compare_transactions(expected, actual, packet_num, edit_instr)
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

    def model(self, pkt_data: bytes, edit_instr: EditInstruction) -> Axi4StreamTransaction:
        """Generate expected output by applying packet byte edits."""
        out = bytearray(pkt_data)
        if edit_instr.edit_enable:
            for i in range(self.edit_bytes):
                if (edit_instr.edit_mask >> i) & 0x1:
                    byte_pos = edit_instr.edit_offset + i
                    if 0 <= byte_pos < len(out):
                        out[byte_pos] = edit_instr.edit_data[i]

        expected_tr = Axi4StreamTransaction(TDATA=bytes(out))
        self.expected_output.append(expected_tr)
        self.edit_instr_map[self.pkts_sent] = edit_instr
        self.pkts_sent += 1
        return expected_tr

    async def send_packet_with_edit(self, pkt_data: bytes, edit_instr: EditInstruction):
        """Send packet via AXI-Stream with edit instruction."""
        data_width = len(self.rx_driver.bus.TDATA) // 8
        word_cnt = (len(pkt_data) + data_width - 1) // data_width

        edit_data_width = len(self.rx_driver.bus.EDIT_DATA)
        edit_offset_width = len(self.rx_driver.bus.EDIT_OFFSET)
        edit_mask_width = len(self.rx_driver.bus.EDIT_MASK)
        edit_enable_width = len(self.rx_driver.bus.EDIT_ENABLE)

        edit_data_int = int.from_bytes(edit_instr.edit_data, byteorder="little")

        edit_data_encoded = 0
        edit_offset_encoded = 0
        edit_mask_encoded = 0
        edit_enable_encoded = 0
        for _ in range(word_cnt):
            edit_data_encoded = (edit_data_encoded << edit_data_width) + edit_data_int
            edit_offset_encoded = (edit_offset_encoded << edit_offset_width) + edit_instr.edit_offset
            edit_mask_encoded = (edit_mask_encoded << edit_mask_width) + edit_instr.edit_mask
            edit_enable_encoded = (edit_enable_encoded << edit_enable_width) + edit_instr.edit_enable

        rx_tr = Axi4StreamTransactionWithEdit(
            TDATA=pkt_data,
            EDIT_DATA=edit_data_encoded,
            EDIT_OFFSET=edit_offset_encoded,
            EDIT_MASK=edit_mask_encoded,
            EDIT_ENABLE=edit_enable_encoded,
        )
        expected = self.model(pkt_data, edit_instr)

        cocotb.log.debug(
            f"Sending packet {self.pkts_sent}: len={len(pkt_data)}, words={word_cnt}, "
            f"edit_offset={edit_instr.edit_offset}, edit_mask=0x{edit_instr.edit_mask:X}, "
            f"edit_enable={edit_instr.edit_enable}, expected_out_len={len(expected.TDATA)}"
        )

        self.rx_driver.append(rx_tr)
