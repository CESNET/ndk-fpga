# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_driver, uvm_analysis_port
from .sequences import HashSeqEmptyItem


class HashUVMDriver(uvm_driver):
    def build_phase(self):
        self.ap  = uvm_analysis_port("ap", self)

    async def run_phase(self):
        await self.parent.dut.reset()

        while True:
            transaction = await self.seq_item_port.get_next_item()
            self.parent.dut.driver.append(transaction)

            if not isinstance(transaction, HashSeqEmptyItem):
                self.ap.write(transaction)

            self.seq_item_port.item_done()
