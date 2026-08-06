# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_HEAD_TRIMMER component.

The trim instruction (TRIM_LENGTH and TRIM_ENABLE) is sampled only
during the FIRST word of each packet. For remaining words, these
signals are ignored.
"""

import cocotb
import logging
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.protocol import Axi4StreamProtocol, optional_signal
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.hex_formatter import format_bytes
from cocotb.types import LogicArray, Logic
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


class Axi4StreamProtocolWithTrim(Axi4StreamProtocol):
    TRIM_LENGTH: LogicArray = optional_signal(put_with="TRIM_ENABLE")
    TRIM_ENABLE: Logic      = optional_signal(put_with="TVALID")


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
        msg += "\n" + format_bytes(expected.TDATA, label="Expected output bytes") + "\n"
    if hasattr(actual, 'TDATA') and actual.TDATA:
        msg += "\n" + format_bytes(actual.TDATA, label="Actual output bytes") + "\n"

    return False, msg


class Testbench:
    """Testbench for AXIS_HEAD_TRIMMER component."""

    def __init__(self, dut, debug: bool = False, rate_limiter_config: dict = {}):
        self.dut = dut
        self.pkt_mtu = int(dut.PKT_MTU.value) if hasattr(dut, 'PKT_MTU') else 9216

        self.rx_driver = Axi4StreamMaster(self.dut, "RX_AXI", dut.CLK, protocol=Axi4StreamProtocolWithTrim, rate_limiter_config=rate_limiter_config)
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
            self.rx_driver.log.setLevel(logging.DEBUG)
            self.tx_monitor.log.setLevel(logging.DEBUG)

    async def reset(self):
        self.dut.RESET.value = 1
        self.dut.TX_AXI_TREADY.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    def model(self, pkt_data: bytes, trim_instr: TrimInstruction) -> Axi4StreamTransaction:
        """Generate expected output by applying trim to packet data."""
        if trim_instr.trim_enable and trim_instr.trim_length > 0:
            actual_trim = min(trim_instr.trim_length, len(pkt_data) - 1)
            trimmed_data = pkt_data[actual_trim:]
        else:
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

        rx_tr = Axi4StreamTransactionWithTrim(
            TDATA=pkt_data,
            TRIM_LENGTH=trim_instr.trim_length,
            TRIM_ENABLE=trim_instr.trim_enable
        )
        expected = self.model(pkt_data, trim_instr)

        cocotb.log.debug(f"Sending packet {self.pkts_sent}: len={len(pkt_data)}, words={word_cnt}, "
                         f"trim_len={trim_instr.trim_length}, trim_en={trim_instr.trim_enable}, "
                         f"expected_out_len={len(expected.TDATA)}")

        self.rx_driver.append(rx_tr)
