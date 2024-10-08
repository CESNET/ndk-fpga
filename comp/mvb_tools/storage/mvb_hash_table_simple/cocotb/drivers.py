# drivers.py: Specialzed MVBDriver for MVB_HASH_TABLE_SIMPLE
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.mvb.drivers import MVBDriver


class MVB_HASH_TABLE_SIMPLE_Driver(MVBDriver):
    _signals = {"data": "key", "vld": "vld", "src_rdy": "src_rdy", "dst_rdy": "dst_rdy"}
