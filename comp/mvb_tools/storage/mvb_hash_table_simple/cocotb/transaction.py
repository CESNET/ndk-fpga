# SPDX-License-Identifier: BSD-3-Clause
# Specialized MVB transaction used for retrieving data from MVB_HASH_TABLE_SIMPLE component.
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>


from dataclasses import dataclass
from cocotbext.ofm.mvb.transaction import MvbTransaction


@dataclass
class MvbResTrHashTableSimple(MvbTransaction):
    data  : int = 0
    match : int = 0

    def __eq__(self, other):
        if isinstance(other, type(self)):
            # If a match occurs, the match and data of the two transactions will be compared. If not, only matches
            # will be compared (because if a hash collision occurs, the returned data are invalid).
            if self.match:
                return self.match == other.match and self.data == other.data
            else:
                return self.match == other.match

        else:
            return False


@dataclass
class MvbReqTrHashTableSimple(MvbTransaction):
    key : int = 0
