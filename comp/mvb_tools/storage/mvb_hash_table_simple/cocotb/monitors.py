# monitors.py: Specialzed MVBMonitor for MVB_HASH_TABLE_SIMPLE
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.mvb.monitors import MVBMonitor


class MVB_HASH_TABLE_SIMPLE_Monitor(MVBMonitor):
    _signals = ["data", "match", "vld", "src_rdy", "dst_rdy"]

    def receive_data(self, data, offset):
        match_val = self.bus.match.value
        match_val.big_endian = False

        self.log.debug(f"MATCH: {match_val}")

        if match_val[offset] == 1:
            self._recv((data[offset*self._item_width:(offset+1)*self._item_width], 1))
        else:
            self._recv((self._item_width * b'\x00', 0))
