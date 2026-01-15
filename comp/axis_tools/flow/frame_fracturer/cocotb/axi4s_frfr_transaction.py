# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from typing import List

from dataclasses import dataclass
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction


@dataclass
class Axi4sFrfrTransaction(Axi4StreamTransaction):
    """Custom Axi4Stream transaction for the AXIS_FRAME_FRACTURER Cocotb test."""

    FRACTURE_EN : List[int] = 0
    FRACTURE_OFFSET : List[int] = 0
