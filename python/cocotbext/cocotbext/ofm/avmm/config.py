# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from dataclasses import dataclass
from enum import Enum


class AvalonMMDataUnits(Enum):
    symbols = 0
    words   = 1


class AvalonMMTimeUnits(Enum):
    cycles = 0
    nanoseconds = 1


@dataclass
class AvalonMMParams:
    addressUnits                    : AvalonMMDataUnits = AvalonMMDataUnits.words
    alwaysBurstMaxBurst             : bool              = False
    burstcountUnits                 : AvalonMMDataUnits = AvalonMMDataUnits.words
    burstOnBurstBoundariesOnly      : bool              = False
    constantBurstBehavior           : bool              = False
    holdTime                        : int               = 0                        # 0 - 1000
    linewrapBursts                  : bool              = False
    maximumPendingReadTransactions  : int               = 1                        # 1 - 64
    maximumPendingWriteTransactions : int               = 0                        # 0 - 64
    minimumResponseLatency          : int               = 1
    readLatency                     : int               = 0                        # 0 - 63
    readWaitTime                    : int               = 0                        # 0 - 1000
    setupTime                       : int               = 0                        # 0 - 1000
    timingUnits                     : AvalonMMTimeUnits = AvalonMMTimeUnits.cycles
    waitrequestAllowance            : int               = 0
    writeWaitTime                   : int               = 0                        # 0 - 1000
