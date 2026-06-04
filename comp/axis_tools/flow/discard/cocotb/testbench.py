# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_DISCARD component.

The discard control signal (RX_AXI_DISCARD) is sampled only during the
FIRST word of each packet. When asserted at SOP, the entire packet is
dropped and not forwarded to the TX interface.
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.hex_formatter import format_bytes
from dataclasses import dataclass
from typing import List


@dataclass
class DiscardInstruction:
    """Discard instruction for a packet."""
    discard: int = 0


@dataclass
class Axi4StreamTransactionWithDiscard(Axi4StreamTransaction):
    """Axi4Stream transaction with DISCARD signal."""
    DISCARD: int = 0


class Axi4StreamMasterWithDiscard(Axi4StreamMaster):
    """Axi4StreamMaster with support for DISCARD signal."""
    _optional_signals = ["TLAST", "TKEEP", "TUSER", "DISCARD"]


def _compare_transactions(expected: Axi4StreamTransaction, actual: Axi4StreamTransaction,
                          packet_num: int = 0, discard_instr: DiscardInstruction = None,
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
    if discard_instr is not None:
        lines.append(f"#  Discard instruction: DISCARD={discard_instr.discard}")
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
    """Testbench for AXIS_DISCARD component."""

    def __init__(self, dut, debug: bool = False):
        self.dut = dut

        self.rx_driver = Axi4StreamMasterWithDiscard(dut, "RX_AXI", dut.CLK)
        self.tx_monitor = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.pkts_sent = 0
        self.pkts_expected = 0
        self.expected_output: List[Axi4StreamTransaction] = []
        self.packet_bytes_map: dict = {}
        self.discard_instr_map: dict = {}

        self.scoreboard = Scoreboard(dut)

        def compare_wrapper(actual):
            """Compare actual output with expected, providing detailed mismatch info."""
            if not self.expected_output:
                cocotb.log.error("Received unexpected packet")
                return
            expected = self.expected_output.pop(0)
            packet_num = self.pkts_sent - len(self.expected_output) - (self.pkts_sent - self.pkts_expected)
            expected.packet_bytes = self.packet_bytes_map.get(packet_num - 1, b'')
            discard_instr = self.discard_instr_map.get(packet_num - 1)
            orig_len = len(expected.packet_bytes) if hasattr(expected, 'packet_bytes') else 0
            match, msg = _compare_transactions(expected, actual, packet_num, discard_instr, orig_len)
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

    def model(self, pkt_data: bytes, discard_instr: DiscardInstruction) -> Axi4StreamTransaction:
        """Generate expected output by applying discard decision to packet data.

        If discard is set, the packet is dropped (no output expected).
        If discard is not set, the packet passes through unchanged.
        """
        self.packet_bytes_map[self.pkts_sent] = pkt_data
        self.discard_instr_map[self.pkts_sent] = discard_instr

        if discard_instr.discard:
            # Packet is discarded - no expected output
            expected_tr = None
        else:
            # Packet passes through unchanged
            expected_tr = Axi4StreamTransaction(TDATA=pkt_data)
            expected_tr.packet_bytes = pkt_data
            self.expected_output.append(expected_tr)
            self.pkts_expected += 1

        self.pkts_sent += 1

        return expected_tr

    async def send_packet_with_discard(self, pkt_data: bytes, discard_instr: DiscardInstruction):
        """Send packet via AXI-Stream with discard instruction.

        DISCARD value is encoded for each word: first word has the value, rest have zeros.
        This matches the convention that DISCARD is sampled only at SOP.
        """
        data_width = len(self.rx_driver.bus.TDATA) // 8
        word_cnt = (len(pkt_data) + data_width - 1) // data_width

        discard_width = len(self.rx_driver.bus.DISCARD)

        # Encode discard values for each word (value on first word, zeros on rest)
        discard_encoded = 0
        for i in range(word_cnt):
            word_discard = discard_instr.discard if i == 0 else 0
            discard_encoded = (discard_encoded << discard_width) + word_discard

        rx_tr = Axi4StreamTransactionWithDiscard(
            TDATA=pkt_data,
            DISCARD=discard_encoded
        )
        self.model(pkt_data, discard_instr)

        action = "DISCARD" if discard_instr.discard else "PASS"
        cocotb.log.debug(f"Sending packet {self.pkts_sent}: len={len(pkt_data)}, words={word_cnt}, "
                         f"action={action}")

        self.rx_driver.append(rx_tr)
