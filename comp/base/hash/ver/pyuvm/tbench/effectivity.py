# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_scoreboard, uvm_tlm_analysis_fifo, uvm_get_port


class Effectivity(uvm_scoreboard):
    def build_phase(self):
        self.consistency_errors = 0
        self.collision_errors   = 0

        self.consistency = dict()
        self.collisions  = dict()

        self._key_queue  = uvm_tlm_analysis_fifo("key_queue", self)
        self._hash_queue = uvm_tlm_analysis_fifo("hash_queue", self)
        self._key_port   = uvm_get_port("key_port", self)
        self._hash_port  = uvm_get_port("hash_port", self)
        self.key_export  = self._key_queue.analysis_export
        self.hash_export = self._hash_queue.analysis_export

    def connect_phase(self):
        self._key_port.connect(self._key_queue.get_export)
        self._hash_port.connect(self._hash_queue.get_export)

    def extract_phase(self):
        while self._key_port.can_get():
            _, key_transaction = self._key_port.try_get()
            got_success, hash_transaction = self._hash_port.try_get()

            if not got_success:
                break

            key  = key_transaction.key
            seed = key_transaction.seed
            hash = hash_transaction["hash"]

            if (key, seed) not in self.consistency.keys():
                self.consistency[(key, seed)] = set()

            self.consistency[(key, seed)].add(hash)

            if hash not in self.collisions.keys():
                self.collisions[hash] = dict()

            if seed not in self.collisions[hash].keys():
                self.collisions[hash][seed] = set()

            self.collisions[hash][seed].add(key)

    def report_phase(self):
        for key_seed, hashes in self.consistency.items():
            key, seed = key_seed

            if len(hashes) > 1:
                self.logger.error(f"Inconsistencies found! Combination of {key=} and {seed=} produce different {hashes=}!")
                self.consistency_errors += len(hashes) - 1

        for hash, seed_dict in self.collisions.items():
            for seed, keys in seed_dict.items():
                if len(keys) > 1:
                    self.logger.error(f"Collisions found! Same {hash=} was produced by combination of {seed=} and {keys=}!")
                    self.collision_errors += len(keys) - 1

        self.logger.info(f"Found {self.consistency_errors} inconsistencies and {self.collision_errors} collisions.")
