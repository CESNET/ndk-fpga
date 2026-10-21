# model.py: Reference model of the VERSAL_PS_CTRL verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Register map, address window translation and the register block model."""

from dataclasses import dataclass, field

# MI (host software) register offsets
STATUS = 0x000
UPPER_ADDR = 0x004
LOWER_ADDR = 0x008
BMC_STATUS = 0x00C
BMC_CONTROL = 0x010
BMC_ERASE_START = 0x014
BMC_ERASE_SIZE = 0x018
WINDOW = 0x800
WINDOW_SIZE = 0x800
MI_SPACE = 0x1000

BMC_REGS = ("status", "control", "erase_start", "erase_size")

# MI offset and PS (AXI4-Lite) offset of each BMC register
BMC_MI_OFFSET = {"status": BMC_STATUS, "control": BMC_CONTROL, "erase_start": BMC_ERASE_START, "erase_size": BMC_ERASE_SIZE}
BMC_PS_OFFSET = {"status": 0x000, "control": 0x004, "erase_start": 0x008, "erase_size": 0x00C}

# The side whose write is kept when the host and the PS write the same register in the same cycle
BMC_WRITE_PRIORITY = {"status": "ps", "control": "host", "erase_start": "host", "erase_size": "host"}

STATUS_BUSY = 0x1
STATUS_ADDR64 = 0x2

DNA_BASE = 0xF125_0020
DNA_WORDS = 4


def window_address(upper: int, lower: int, offset: int, addr64: bool, axi_addr_width: int) -> int:
    """PS address of an MI access to the window at MI offset ``offset`` (0x800 - 0xFFF)."""
    addr = (lower & 0xFFFF_F800) | (offset & 0x7FC)
    if addr64:
        addr |= upper << 32
    return addr & (2**axi_addr_width - 1)


def fpga_id_from_words(words: list[int]) -> int:
    return sum(word << (32 * index) for index, word in enumerate(words))


def bmc_by_mi_offset(offset: int) -> str | None:
    for name, off in BMC_MI_OFFSET.items():
        if offset & 0x7FF == off:
            return name
    return None


def bmc_by_ps_offset(offset: int) -> str | None:
    for name, off in BMC_PS_OFFSET.items():
        if offset & 0x7FF == off:
            return name
    return None


@dataclass
class RegisterModel:
    """Registers of VERSAL_PS_ACCESS, updated in the cycle the write reaches the register block.

    BMC registers are not reset (only initialised by the configuration), the
    window address registers are cleared by AXI_LITE_RESET.
    """
    addr64: bool
    upper: int = 0
    lower: int = 0
    bmc: dict[str, int] = field(default_factory=lambda: {name: 0 for name in BMC_REGS})
    collisions: dict[str, int] = field(default_factory=lambda: {name: 0 for name in BMC_REGS})

    def reset(self) -> None:
        self.upper = 0
        self.lower = 0

    def host_read(self, offset: int) -> int:
        """Expected value of a host register read; the BUSY bit is checked separately."""
        offset &= 0x7FF
        if offset == STATUS:
            return STATUS_ADDR64 if self.addr64 else 0
        if offset == UPPER_ADDR:
            return self.upper
        if offset == LOWER_ADDR:
            return self.lower
        name = bmc_by_mi_offset(offset)
        return self.bmc[name] if name else 0

    def ps_read(self, offset: int) -> int:
        name = bmc_by_ps_offset(offset)
        return self.bmc[name] if name else 0

    def write_cycle(self, host: tuple[int, int] | None, ps: tuple[int, int] | None) -> None:
        """Applies the host and PS register writes of one clock cycle, (offset, data) each."""
        host_reg = bmc_by_mi_offset(host[0]) if host else None
        ps_reg = bmc_by_ps_offset(ps[0]) if ps else None

        if host is not None:
            offset = host[0] & 0x7FF
            if offset == UPPER_ADDR:
                self.upper = host[1]
            elif offset == LOWER_ADDR:
                self.lower = host[1]

        if host_reg is not None and host_reg == ps_reg:
            self.collisions[host_reg] += 1
            winner = host if BMC_WRITE_PRIORITY[host_reg] == "host" else ps
            assert winner is not None
            self.bmc[host_reg] = winner[1]
            return

        if host_reg is not None and host is not None:
            self.bmc[host_reg] = host[1]
        if ps_reg is not None and ps is not None:
            self.bmc[ps_reg] = ps[1]
