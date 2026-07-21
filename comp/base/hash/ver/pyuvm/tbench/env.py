# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_env, uvm_sequencer, ConfigDB
from .drivers import HashUVMDriver
from .monitors import HashUVMMonitor
from .scoreboard import Scoreboard
from .coverage import Coverage
from .effectivity import Effectivity
from .latency import Latency


class HashEnv(uvm_env):
    def build_phase(self):
        self.dut         = ConfigDB().get(None, "", "DUT")
        self.sequencer   = uvm_sequencer("sequencer", self)
        self.driver      = HashUVMDriver("driver", self)
        self.monitor     = HashUVMMonitor("monitor", self)
        self.scoreboard  = Scoreboard("scoreboard", self)
        self.coverage    = Coverage("coverage", self)
        self.effectivity = Effectivity("effectivity", self)
        self.latency     = Latency("latency", self)

        ConfigDB().set(None, "*", "SEQR", self.sequencer)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.sequencer.seq_item_export)
        self.driver.ap.connect(self.scoreboard.expected_export)
        self.driver.ap.connect(self.coverage.analysis_export)
        self.driver.ap.connect(self.effectivity.key_export)
        self.driver.ap.connect(self.latency.key_export)
        self.monitor.ap.connect(self.scoreboard.result_export)
        self.monitor.ap.connect(self.effectivity.hash_export)
        self.monitor.ap.connect(self.latency.hash_export)
