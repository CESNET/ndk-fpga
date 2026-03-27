# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for AXIS_PACKET_CONCATENATOR component."""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction


def _format_bytes(data: bytes, bytes_per_line: int = 32) -> str:
    """Format bytes as a readable string with hex values separated by spaces.

    Args:
        data: The bytes data to format.
        bytes_per_line: Number of bytes to display per line.

    Returns:
        A formatted string with hex values separated by spaces.
    """
    if not isinstance(data, bytes):
        return str(data)

    lines = []
    for i in range(0, len(data), bytes_per_line):
        chunk = data[i:i + bytes_per_line]
        # Format each byte as two-digit hex with space separator
        hex_bytes = ' '.join(f'{b:02x}' for b in chunk)
        # Add offset at the beginning of each line
        lines.append(f"  0x{i:04x}: {hex_bytes}")

    return '\n'.join(lines) if lines else "  (empty)"


def _format_transaction(transaction, label: str) -> str:
    """Format a transaction for display.

    Args:
        transaction: The transaction to format (expected or received).
        label: Label to display (e.g., "MODEL" or "DUT").

    Returns:
        A formatted string representation of the transaction.
    """
    # Get TDATA from transaction
    if hasattr(transaction, 'TDATA'):
        data = transaction.TDATA
    else:
        data = str(transaction)

    if isinstance(data, bytes):
        header = f"{label} ({len(data)} bytes):"
        body = _format_bytes(data, bytes_per_line=32)
        return f"{header}\n{body}"
    else:
        return f"{label}:\n  {data}"


def _compare_transactions(expected, actual, transaction_num: int = 0) -> tuple:
    """Compare two transactions and return detailed mismatch output.

    Args:
        expected: The expected transaction from model.
        actual: The actual transaction from DUT.
        transaction_num: Transaction number for display.

    Returns:
        Tuple of (match: bool, message: str).
    """
    match = expected == actual

    if match:
        return True, ""

    lines = []
    lines.append("")
    lines.append("=" * 70)
    lines.append(f"Transaction #{transaction_num}: MISMATCH DETECTED")
    lines.append("=" * 70)

    msg = "\n".join(lines)

    # Print expected (model) transaction
    msg += "\n" + _format_transaction(expected, "MODEL (Expected)")
    msg += "\n" + "-" * 70 + "\n"
    # Print received (DUT) transaction
    msg += _format_transaction(actual, "DUT (Received)")
    msg += "\n" + "=" * 70

    return False, msg


class Testbench:
    """Testbench for AXIS_PACKET_CONCATENATOR component."""

    def __init__(self, dut, debug=False):
        self.dut = dut
        self.rx0_drv = Axi4StreamMaster(dut, "RX0_AXIS", dut.CLK)
        self.rx1_drv = Axi4StreamMaster(dut, "RX1_AXIS", dut.CLK)
        self.tx_mon = Axi4Stream(dut, "TX_AXIS", dut.CLK, trans_type=Axi4StreamTransaction)
        self.backpressure = BitDriver(dut.TX_AXIS_TREADY, dut.CLK)

        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.compared = 0

        def compare_wrapper(actual):
            """Compare actual output with expected, providing detailed mismatch info."""
            if not self.expected_output:
                cocotb.log.error("Received unexpected packet")
                return
            expected = self.expected_output.pop(0)
            self.compared += 1
            match, msg = _compare_transactions(expected, actual, self.compared)
            if not match:
                cocotb.log.error(msg)
                self.scoreboard.errors += 1
                raise AssertionError(f"Transaction mismatch detected:\n{msg}")
            # Log success for each transaction
            cocotb.log.debug(f"Transaction #{self.compared}: OK ({len(actual.TDATA)} bytes)")
            return match

        self.scoreboard.add_interface(self.tx_mon, self.expected_output, compare_fn=compare_wrapper)

        if debug:
            self.rx0_drv.log.setLevel(cocotb.logging.DEBUG)
            self.rx1_drv.log.setLevel(cocotb.logging.DEBUG)
            self.tx_mon.log.setLevel(cocotb.logging.DEBUG)

    def model(self, rx0_tr: Axi4StreamTransaction, rx1_tr: Axi4StreamTransaction):
        """Model of the DUT - concatenates two packets"""
        concatenated = rx0_tr.TDATA + rx1_tr.TDATA
        tx_tr = Axi4StreamTransaction()
        tx_tr.TDATA = concatenated
        self.expected_output.append(tx_tr)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)
