# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from cocotbext.ofm.mfb.monitors import MFBMonitor

from transaction import PprData


class PprMonitor(MFBMonitor):
    """Monitor for the USER_RESP_MFB interface."""

    _optional_signals = ["id"]

    def __init__(self, entity, name, clock, array_idx=None, trans_type=PprData) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx, trans_type=trans_type)
