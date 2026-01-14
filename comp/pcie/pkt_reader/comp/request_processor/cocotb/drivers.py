# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from cocotbext.ofm.mvb.drivers import MVBDriver


class PprDriver(MVBDriver):
    _optional_signals = ["id", "address", "length"]
