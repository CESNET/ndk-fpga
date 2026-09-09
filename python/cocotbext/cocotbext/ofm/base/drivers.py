# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondřej Schwarz <ondrejschwarz@cesnet.cz>

from typing import Optional
from copy import copy

import cocotb
import cocotb.utils
import cocotb_bus.drivers as cbd
from cocotb.triggers import RisingEdge

from .bus_fixup import do_fix
from .types import LogicArray2D
from .transaction import BaseTransaction, Transaction, IdleTransaction, IdleTransactionFactory
from .generators import IdleGenerator, ItemRateLimiter

do_fix()


class BusDriver(cbd.BusDriver):
    """
    BusDriver adds common functionality like

     * RisingEdge clock event (self._clk_re)
     * Configuration (self._cfg) can be used for example to configure specific idle generator
     * Idle generator (default is IdleGenerator, which doesn't generates any idles)
    """

    def __init__(self, entity, name, clock, array_idx=None, **kwargs):
        self._clk_re = RisingEdge(clock)

        self._cfg = dict(
            clk_freq=kwargs.get("clk_freq"),
        )

        self._idle_gen = IdleGenerator()
        self._idle_tr = IdleTransaction()

        # cocotb 2.0-only defines
        if cocotb.__version__ >= "2.0.0":
            from .bus_fixup import BusProxy

            # initiate without using array idx, which causes problems in cocotb 2.0
            super().__init__(entity, name, clock, array_idx=None)

            # replace bus with bus proxy
            self.bus = BusProxy(self.bus, array_idx)

        else:
            super().__init__(entity, name, clock, array_idx=array_idx)

        self._cfg_update()

    def _cfg_update(self, **kwargs):
        self._cfg.update(kwargs)

        self._idle_gen.configure(**self._cfg)

    def set_idle_generator(self, generator):
        self._idle_gen = generator
        self._cfg_update()

    async def _measure_clkfreq(self, trigger=None):
        """
        Measure the clock frequency by passing the simulation time

        This can simplify the configuration of some idle generators.
        """

        if trigger is None:
            trigger = self._clk_re

        t1 = cocotb.utils.get_sim_time('ps')
        await trigger
        t2 = cocotb.utils.get_sim_time('ps')

        clk_freq = 1e12 / (t2 - t1)
        self._cfg_update(clk_freq=clk_freq)
        return clk_freq


if cocotb.__version__ >= "2.0.0":
    from cocotb.types import LogicArray
    from cocotb.handle import LogicObject
    from cocotb.queue import Queue
    from .protocol import BusProtocol
    from dataclasses import dataclass

    class ModularBusDriver:
        """Base class for bus drivers built on top of a :class:`BusProtocol` (cocotb 2.0+).

        The driver resolves the bus signals via the given ``protocol`` and
        automatically transfers values between transactions and the DUT
        signals: attributes of a transaction matching the protocol's signal
        names are written to the bus, without the need to hand-code signal
        assignments for every bus variant.

        Driving model:
            - Transactions are queued with :meth:`append` (must be instances
              of :class:`BaseTransaction`).
            - An internal generator (:meth:`_fetch_transaction`) pulls
              transactions from the queue, inserting idle transactions
              produced by the idle generator/factory between them.
            - The main loop (:meth:`_main_loop`) drives each transaction
              onto the bus word by word: :meth:`_split_transaction` stages
              values into ``self.state`` and yields once per clock cycle,
              after which the state is written to the DUT signals.

        Subclasses (e.g. ``MVBDriver``, ``MFBDriver``) typically override
        :meth:`_init_state`, :meth:`_clear_signals`, :meth:`_split_transaction`
        and :meth:`_get_sent_items` to implement the bus-specific behavior.

        Args:
            dut: The DUT handle (cocotb hierarchy object).
            name: Bus name prefix used to resolve signal names on the DUT.
            clock: Clock signal driving the bus.
            protocol: :class:`BusProtocol` subclass describing the bus.
            protocol_kwargs: Extra keyword arguments passed to the protocol.
            array_idx: Index into an arrayed bus (multi-instance interfaces).
            generics_prefix: Prefix prepended to generic names on the DUT.
            separator: Separator between the bus name and signal names.
            clk_freq: Clock frequency in Hz (used by some idle generators).
            idle_factory: Factory producing idle transactions when the queue
                is empty or when the idle generator requests a gap.
        """

        bus   : BusProtocol
        state : dataclass

        def __init__(
            self,
            dut,
            name: str,
            clock: LogicObject,
            protocol: type = BusProtocol,
            protocol_kwargs: dict = {},
            array_idx: Optional[int] = None,
            generics_prefix: str = "",
            separator: str = "_",
            clk_freq: Optional[float] = None,
            idle_factory=IdleTransactionFactory(),
            no_default_rate_limiter=False,
            rate_limiter_config: dict = dict(rate_percentage=30, random_idles=True, max_idles=3, zero_idles_chance=80)
        ):

            self._init_bus(protocol, dut, name, separator, array_idx, generics_prefix, **protocol_kwargs)
            self._init_state()

            self.clock     : LogicObject   = clock
            self.array_idx : Optional[int] = array_idx

            self._clk_re: RisingEdge = RisingEdge(clock)
            self._send_queue: Queue  = Queue()
            self._transactions       = self._fetch_transaction()

            self._item_cnt   : int = 0
            self._sent_items : int = 0

            # idle generator settings
            self._cfg = dict(
                clk_freq=clk_freq,
            )

            # default idle generator that actually generates idles
            self._idle_gen = IdleGenerator() if no_default_rate_limiter else ItemRateLimiter(**rate_limiter_config)
            self._idle_fac = idle_factory

            self._cfg_update()

            self._clear_signals()
            self._write_to_bus()
            cocotb.start_soon(self._main_loop())

        @property
        def item_cnt(self):
            """Number of items (bus-specific units) sent so far."""
            return self._item_cnt

        def append(self, transaction: Transaction):
            """Queue a transaction to be driven onto the bus.

            The transaction must be an instance of :class:`BaseTransaction`.
            """
            self._send_queue.put_nowait(transaction)

        def _init_bus(self, protocol, *args, **kwargs):
            self.bus = protocol(*args, **kwargs)

        def _init_state(self):
            """Initialize the staged signal state; subclasses override with a bus-specific dataclass."""
            self.state = dataclass()

        def _clear_signals(self):
            self._auto_clear_signals()

        async def _fetch_transaction(self):
            """Generator yielding transactions and idle gaps in driving order.

            Pulls transactions from the send queue. When the queue is empty,
            idle transactions from the idle factory are yielded instead.
            Before each queued transaction, additional idle transactions are
            inserted as requested by the idle generator.
            """
            while True:
                while self._send_queue.empty():
                    yield self._idle_fac.make()

                while not self._send_queue.empty():
                    transaction = await self._send_queue.get()

                    assert isinstance(transaction, BaseTransaction), f"Transaction must be an instance of BaseTransation, not {type(transaction)}."

                    idle_count = self._idle_gen.get(transaction)

                    for _ in range(idle_count):
                        yield self._idle_fac.make()

                    yield copy(transaction)

        async def _split_transaction(self, transaction: Transaction):
            """Stage transaction values into ``self.state``, yielding once per bus word.

            Each ``yield`` hands control back to the main loop, which writes
            the staged state to the DUT and waits one clock cycle. Subclasses
            override this to split multi-word transactions into individual
            bus words.
            """
            self._auto_set_signals(transaction)

        def _write_to_bus(self):
            self._auto_write_signals()

        async def _send_to_bus(self):
            """Write the staged state to the DUT signals and wait for the next clock edge."""
            self._write_to_bus()
            await self._clk_re

        async def _handle_idle_transaction(self):
            """Drive one idle cycle: clear the signals and wait for the next clock edge."""
            self._clear_signals()
            self._write_to_bus()
            await self._clk_re

        def _get_sent_items(self) -> int:
            """Return how many items were sent in the last bus word; subclasses override."""
            return 1

        async def _main_loop(self):
            """Main driving loop: consume transactions and drive them onto the bus."""
            async for transaction in self._transactions:
                if isinstance(transaction, IdleTransaction):
                    await self._handle_idle_transaction()
                    self._idle_gen.put(transaction, items=1, end=True)
                    continue

                sent_items = 0

                async for _ in self._split_transaction(transaction):
                    await self._send_to_bus()
                    items = self._get_sent_items()
                    self._item_cnt += items
                    sent_items += items
                    self._clear_signals()
                    self._write_to_bus()

                self._idle_gen.put(transaction, items=sent_items, end=True)

        def _auto_clear_signals(self):
            """Sets all signals to X."""
            for name in self.bus.signals.keys():
                if hasattr(self.state, name):
                    value = getattr(self.bus, name)
                    width = len(value)

                    if isinstance(value, LogicArray2D):
                        width *= len(value.item_range)
                    elif isinstance(value, bytes):
                        width *= 8

                    setattr(self.state, name, LogicArray("X" * width))

        def _auto_clear_optional_signals(self):
            """Sets all optional signals to X."""
            for name in self.bus.optional_signals.keys():
                if hasattr(self.state, name):
                    value = getattr(self.bus, name)
                    width = len(value)

                    if isinstance(value, LogicArray2D):
                        width *= len(value.item_range)
                    elif isinstance(value, bytes):
                        width *= 8

                    setattr(self.state, name, LogicArray("X" * width))

        def _auto_set_signals(self, transaction: Transaction):
            """Automatically assings value to signals present in the transaction."""
            for name in self.bus.signals.keys():
                if hasattr(transaction, name):
                    value = getattr(transaction, name)
                    put_with = self.bus.put_with(name)

                    if put_with is None:
                        continue

                    if getattr(self.state, put_with):
                        setattr(self.state, name, value)

        def _auto_set_optional_signals(self, transaction: Transaction):
            """Automatically assings value to optional signals present in the transaction."""
            for name in self.bus.optional_signals.keys():
                if hasattr(transaction, name):
                    value = getattr(transaction, name)
                    put_with = self.bus.put_with(name)

                    if put_with is None:
                        continue

                    if getattr(self.state, put_with):
                        setattr(self.state, name, value)

        def _auto_write_signals(self):
            """Write all staged signal values from ``self.state`` to the DUT."""
            for name in self.bus.signals.keys():
                if hasattr(self.state, name):
                    value = getattr(self.state, name)
                    setattr(self.bus, name, value)

        def _auto_write_optional_signals(self):
            """Write staged values of optional signals from ``self.state`` to the DUT."""
            for name in self.bus.optional_signals.keys():
                if hasattr(self.state, name):
                    setattr(self.bus, name, getattr(self.state, name))

        def _cfg_update(self, **kwargs):
            self._cfg.update(kwargs)
            self._idle_gen.configure(**self._cfg)

        def set_idle_generator(self, generator):
            """Replace the idle generator (e.g. with ``ItemRateLimiter``) and reconfigure it."""
            self._idle_gen = generator
            self._cfg_update()

        async def _measure_clkfreq(self, trigger=None):
            """
            Measure the clock frequency by passing the simulation time

            This can simplify the configuration of some idle generators.
            """

            if trigger is None:
                trigger = self._clk_re

            t1 = cocotb.utils.get_sim_time('ps')
            await trigger
            t2 = cocotb.utils.get_sim_time('ps')

            clk_freq = 1e12 / (t2 - t1)
            self._cfg_update(clk_freq=clk_freq)
            return clk_freq
