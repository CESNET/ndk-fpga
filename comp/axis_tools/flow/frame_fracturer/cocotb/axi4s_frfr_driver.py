# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#            Ondřej Schwarz <ondrejschwarz@cesnet.cz>

from math import ceil, log2

from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotb.types import Logic, LogicArray
from axi4s_frfr_transaction import Axi4sFrfrTransaction
from axi4s_frfr_protocol import Axi4sFrfrProtocol
from dataclasses import dataclass


class Axi4sFrfrDriver(Axi4StreamMaster):
    bus: Axi4sFrfrProtocol

    @dataclass
    class State(Axi4StreamMaster.State):
        FRACTURE_EN     : Logic      = 0
        FRACTURE_OFFSET : LogicArray = 0

    def __init__(self, *args, protocol=Axi4sFrfrProtocol, **kwargs):
        super().__init__(*args, protocol=protocol, **kwargs)

    def _init_state(self):
        self.state: Axi4sFrfrDriver.State = Axi4sFrfrDriver.State()

    async def _split_transaction(self, transaction: Axi4sFrfrTransaction):
        i: int = 0
        off_w = ceil(log2(len(self.bus.TDATA) // 8))

        async for _ in super()._split_transaction(transaction):
            # Pack per-slot enables into a single bit vector.
            en_packed = 0
            for f, e in enumerate(transaction.FRACTURE_EN[i]):
                en_packed |= (e & 1) << f
            self.state.FRACTURE_EN = en_packed

            # Pack per-slot offsets into a concatenated bit field.
            off_packed = 0
            for f, o in enumerate(transaction.FRACTURE_OFFSET[i]):
                off_packed |= (o & ((1 << off_w) - 1)) << (f * off_w)
            self.state.FRACTURE_OFFSET = off_packed

            i += 1
            yield
