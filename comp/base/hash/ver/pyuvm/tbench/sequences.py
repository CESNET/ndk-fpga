# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_sequence_item, uvm_sequence, ConfigDB
from random import randint
from random import choice as randchoice
from cocotbext.ofm.utils.random import randint_recursive


class HashSeqBaseItem(uvm_sequence_item):
    key  : int = 0
    seed : int = 0
    meta : int = 0

    def to_dict(self) -> dict:
        return {"key": self.key, "seed": self.seed, "meta": self.meta}

    def __eq__(self, other):
        return self.key == other.key and self.seed == other.seed and self.meta == other.meta

    def __str__(self):
        return f"HashSeqItem(key={self.key}, seed={self.seed}, meta={self.meta})"

    def __repr__(self):
        return str(self)


class HashSeqEmptyItem(HashSeqBaseItem):
    """Empty item used for spaces."""


class HashSeqItem(HashSeqBaseItem):
    def __init__(self, name: str, key: int = 0, seed: int = 0, meta: int = 0):
        super().__init__(name)
        self.key  = key
        self.seed = seed
        self.meta = meta

    def randomize(self) -> None:
        dut = ConfigDB().get(None, "", "DUT")
        self.key  = randint_recursive(0, dut.key_width)
        self.seed = randint_recursive(0, dut.seed_width)
        self.meta = randint_recursive(0, dut.meta_width)


class HashBaseSequence(uvm_sequence):
    """Base sequence for HashHash component"""

    def __init__(self, name, min_items: int = 1, max_items: int = 512):
        super().__init__(name)
        self.item_count: int = randint(min_items, max_items)


class HashEmptySequence(HashBaseSequence):
    async def body(self):
        for _ in range(self.item_count):
            transaction = HashSeqEmptyItem("hash_empty_seqitem")
            await self.start_item(transaction)
            await self.finish_item(transaction)


class HashRandomSequence(HashBaseSequence):
    async def body(self):
        for _ in range(self.item_count):
            transaction = HashSeqItem("hash_seqitem")
            transaction.randomize()
            await self.start_item(transaction)
            await self.finish_item(transaction)


class HashMaxSequence(HashBaseSequence):
    async def body(self):
        dut = ConfigDB().get(None, "", "DUT")
        max_key = 2**dut.key_width-1
        max_seed = 2**dut.seed_width-1
        max_meta = 2**dut.meta_width-1

        for _ in range(self.item_count):
            transaction = HashSeqItem("hash_seq_item", key=max_key, seed=max_seed, meta=max_meta)
            await self.start_item(transaction)
            await self.finish_item(transaction)


class HashConstSeedSequence(HashBaseSequence):
    def __init__(self, *args, const_seed: int = 0, **kwargs):
        super().__init__(*args, **kwargs)
        self.const_seed: int = const_seed

    async def body(self):
        for _ in range(self.item_count):
            transaction = HashSeqItem("hash_seqitem")
            transaction.randomize()
            transaction.seed = self.const_seed
            await self.start_item(transaction)
            await self.finish_item(transaction)


class TestHashSequencesBase(uvm_sequence):
    def __init__(self, name, min_items: int = 1, max_items: int = 512, seq_count: int = 100, min_empty: int = 0, max_empty: int = 512):
        super().__init__(name)
        self.min_items  : int = min_items
        self.max_items  : int = max_items
        self.seq_count  : int = seq_count
        self.min_empty  : int = min_empty
        self.max_empty  : int = max_empty
        self.item_count : int = 0


class TestHashSequencesConstSeed(TestHashSequencesBase):
    def __init__(self, *args, const_seed: int = 0, **kwargs):
        super().__init__(*args, **kwargs)
        self.const_seed = const_seed

    async def body(self):
        sequencer = ConfigDB().get(None, "", "SEQR")

        for _ in range(self.seq_count):
            max = HashConstSeedSequence("hash_seq_constseed", min_items=self.min_items, max_items=self.max_items, const_seed=self.const_seed)
            self.item_count += max.item_count
            await max.start(sequencer)
            empty = HashEmptySequence("hash_seq_empty", min_items=self.min_empty, max_items=self.max_empty)
            await empty.start(sequencer)


class TestHashSequencesRandom(TestHashSequencesBase):
    async def body(self):
        sequencer = ConfigDB().get(None, "", "SEQR")

        for _ in range(self.seq_count):
            random = HashRandomSequence("hash_seq_random", min_items=self.min_items, max_items=self.max_items)
            self.item_count += random.item_count
            await random.start(sequencer)
            empty = HashEmptySequence("hash_seq_empty", min_items=self.min_empty, max_items=self.max_empty)
            await empty.start(sequencer)


class TestHashSequencesMax(TestHashSequencesBase):
    async def body(self):
        sequencer = ConfigDB().get(None, "", "SEQR")

        for _ in range(self.seq_count):
            max = HashMaxSequence("hash_seq_max", min_items=self.min_items, max_items=self.max_items)
            self.item_count += max.item_count
            await max.start(sequencer)
            empty = HashEmptySequence("hash_seq_empty", min_items=self.min_empty, max_items=self.max_empty)
            await empty.start(sequencer)


class TestHashSequencesAll(TestHashSequencesBase):
    async def body(self):
        sequencer = ConfigDB().get(None, "", "SEQR")
        dut = ConfigDB().get(None, "", "DUT")

        seq_array  = [HashConstSeedSequence, HashRandomSequence, HashMaxSequence]
        seq_kwargs = {HashConstSeedSequence: {"name": "hash_seq_constseed", "const_seed": randint(0, 2**dut.seed_width-1)},
                      HashRandomSequence: {"name": "hash_seq_random"},
                      HashMaxSequence: {"name": "hash_seq_max"}}

        for _ in range(self.seq_count):
            sequence_type = randchoice(seq_array)
            sequence = sequence_type(min_items=self.min_items, max_items=self.max_items, **seq_kwargs[sequence_type])
            self.item_count += sequence.item_count
            await sequence.start(sequencer)
            empty = HashEmptySequence("hash_seq_empty", min_items=self.min_empty, max_items=self.max_empty)
            await empty.start(sequencer)
