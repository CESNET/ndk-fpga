# dram_pkt_capture_regs.py: register access classes of the dram_pkt_capture application
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
"""Register access for the dram_pkt_capture application.

The single definition of the app_status register map, shared by the scripts in
this directory and the top-level cocotb test. Import it instead of copying the
offsets:

    from dram_pkt_capture_regs import AppStatus, RxMacRegs
"""

import nfb


class AppStatus(nfb.BaseComp):
    """app_status register block of one dram_pkt_capture app core."""

    DT_COMPATIBLE = "cesnet,dram_pkt_capture,app_status"

    _REG_STATUS = 0x00
    _REG_ENABLE = 0x04
    _REG_READ_EN = 0x08

    @property
    def dram_full(self) -> bool:
        return bool(self._comp.read32(self._REG_STATUS) & 0x1)

    @property
    def capture_enable(self) -> bool:
        return bool(self._comp.read32(self._REG_ENABLE) & 0x1)

    @property
    def read_enable(self) -> bool:
        return bool(self._comp.read32(self._REG_READ_EN) & 0x1)

    def set_capture_enable(self, en: bool) -> None:
        self._comp.write32(self._REG_ENABLE, int(en))

    def set_read_enable(self, en: bool) -> None:
        self._comp.write32(self._REG_READ_EN, int(en))


class RxMacRegs(nfb.BaseComp):
    """The RX MAC Lite's maximum frame length, which nfb's own RxMac omits."""

    DT_COMPATIBLE = "netcope,rxmac"

    _REG_MAX_FRAME_LEN = 0x34

    def set_max_frame_len(self, length: int) -> None:
        self._comp.write32(self._REG_MAX_FRAME_LEN, length)
