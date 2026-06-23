# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_PACKET_EXTENDER component.

The extension length (RX_AXI_EXT_LEN) is sampled only during the FIRST word
of each packet. The component extends the packet by the given length, shifting
the original payload right by the extension length in bytes. The extension
bytes are not checked by this testbench.
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
class ExtendInstruction:
    """Extend instruction for a packet."""
    ext_len: int = 0


@dataclass
class Axi4StreamTransactionWithExtLen(Axi4StreamTransaction):
    """Axi4Stream transaction with EXT_LEN signal."""
    EXT_LEN: int = 0


class Axi4StreamMasterWithExtLen(Axi4StreamMaster):
    """Axi4StreamMaster with support for the RX_AXI_EXT_LEN signal."""
    _optional_signals = ["TLAST", "TKEEP", "EXT_LEN"]


def _compare_transactions(expected: Axi4StreamTransaction, actual: Axi4StreamTransaction,
                          packet_num: int = 0, ext_instr: ExtendInstruction = None) -> tuple:
    """Compare two AXI4-Stream transactions with detailed mismatch output.

    Only the total output length and the original packet bytes (at the tail of
    the output) are compared. The extension bytes may contain any value.

    The banner reports exactly three pieces of information:
      1. the packet number (progress / identification),
      2. the extend length (the instruction applied to this packet),
      3. the expected vs. actual data (length summary + hex dumps).
    """
    orig_packet = getattr(expected, 'orig_packet', expected.TDATA)
    match = (
        len(expected.TDATA) == len(actual.TDATA)
        and actual.TDATA[-len(orig_packet):] == orig_packet
    )

    if match:
        return True, ""

    lines = []
    lines.append("")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#" + " " * 18 + f"PACKET MISMATCH #{packet_num}" + " " * 27 + "#")
    lines.append("#" + "=" * 64 + "#")
    if ext_instr:
        lines.append(f"#  Extend instruction: EXT_LEN={ext_instr.ext_len}")
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
    """Testbench for AXIS_PACKET_EXTENDER component."""

    def __init__(self, dut, debug: bool = False):
        self.dut = dut
        self.ext_len_width = dut.EXT_LEN_WIDTH.value
        # Maximum extend value supported by the EXT_LEN_WIDTH-bit signal
        self.max_ext_len = 2 ** self.ext_len_width - 1

        self.rx_driver = Axi4StreamMasterWithExtLen(dut, "RX_AXI", dut.CLK)
        self.tx_monitor = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.pkts_sent = 0
        self.expected_output: List[Axi4StreamTransaction] = []

        self.scoreboard = Scoreboard(dut)

        def compare_wrapper(actual):
            """Compare actual output with expected, providing detailed mismatch info."""
            if not self.expected_output:
                cocotb.log.error("Received unexpected packet")
                return
            expected = self.expected_output.pop(0)
            packet_num = self.pkts_sent - len(self.expected_output)
            # ext_instr is attached to the expected transaction by model(),
            # so no external lookup map is required.
            ext_instr = getattr(expected, 'ext_instr', None)
            match, msg = _compare_transactions(expected, actual, packet_num, ext_instr)
            if not match:
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

    def model(self, pkt_data: bytes, ext_instr: ExtendInstruction) -> Axi4StreamTransaction:
        """Generate expected output for a packet extended by ext_len bytes.

        The expected transaction stores the total expected length and the
        original packet bytes; the comparator ignores the value of the extension
        bytes. The extend instruction is attached to the returned transaction so
        the scoreboard comparator can report EXT_LEN on a mismatch without
        needing any external lookup structure.
        """
        extended_data = b'\x00' * ext_instr.ext_len + pkt_data

        expected_tr = Axi4StreamTransaction(TDATA=extended_data)
        expected_tr.ext_instr = ext_instr
        expected_tr.orig_packet = pkt_data
        self.expected_output.append(expected_tr)

        self.pkts_sent += 1

        return expected_tr

    async def send_packet_with_ext(self, pkt_data: bytes, ext_instr: ExtendInstruction):
        """Send packet via AXI-Stream with extension length instruction.

        EXT_LEN is encoded for each word: first word has the value, rest have zeros
        (only SOP is sampled by the DUT).
        """
        data_width = len(self.rx_driver.bus.TDATA) // 8
        word_cnt = (len(pkt_data) + data_width - 1) // data_width

        ext_len_width = len(self.rx_driver.bus.EXT_LEN)

        # Encode EXT_LEN values per word: first word carries ext_len, others zero
        ext_len_encoded = 0
        for i in range(word_cnt):
            word_ext_len = ext_instr.ext_len if (i == 0) else 0
            ext_len_encoded = (ext_len_encoded << ext_len_width) + word_ext_len

        rx_tr = Axi4StreamTransactionWithExtLen(
            TDATA=pkt_data,
            EXT_LEN=ext_len_encoded
        )
        expected = self.model(pkt_data, ext_instr)

        cocotb.log.debug(f"Sending packet {self.pkts_sent}: len={len(pkt_data)}, words={word_cnt}, "
                         f"ext_len={ext_instr.ext_len}, "
                         f"expected_out_len={len(expected.TDATA)}")

        self.rx_driver.append(rx_tr)
