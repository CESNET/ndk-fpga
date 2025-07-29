# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. states. p. o.
# Author(states): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.binary import Binary, BinaryVector
from copy import copy
from enum import Enum
from cocotbext.ofm.avst_pcie.drivers import AvstPcieDriverMaster
from cocotbext.ofm.avst_pcie.monitors import AvstPcieMonitor
from cocotb.queue import PriorityQueue
from typing import Optional
from cocotbext.ofm.utils.math import ceildiv
from cocotbext.ofm.base.proxymonitor import ProxyMonitor
from dataclasses import dataclass
from cocotbext.ofm.pcie.AvstCompleter import RequestHeader
from sys import maxsize


class AvstCreditorStatesTX(Enum):
    START_INIT = 0
    WAITING_FOR_ACK = 1
    DECLARE_CREDITS = 2
    WAITING_1 = 3
    WAITING_2 = 4
    END_INIT = 5
    UPDATE_CREDITS = 6


class AvstCreditorStatesRX(Enum):
    WAITING_FOR_INIT = 0
    RESPOND_WITH_ACK = 1
    UPDATE = 2


class AvstTransactionTypes(Enum):
    # Posted transactions (P): does not require a response
    Posted = 2
    # Non-posted transactions (NP): requires a completion
    NonPosted = 1
    # Completions (CPL): response to non-posted transactions
    Completion = 0


@dataclass
class PcieTransactionTypes:
    MRd  = [0, 128]
    MWr  = [64, 192]
    CplD = [74]


class AvstCreditorTX(BusDriver):
    """Driver controlling the TX side of R-TILE credit interface."""

    _signals = ["init", "update", "update_cnt", "init_ack"]

    def __init__(self, entity, name, clock, credits: list[int], array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._segments: int = len(self.bus.init)
        self._data_len: int = len(self.bus.update_cnt) // self._segments

        """
        This variable works a little different then might be expected. It indicates number
        of credits that have been given or returned to this creditor. So if this value is
        equal of zero, it means that all credits have been declared to the RX component.
        Value higher than zero means, that a) not all credits have been declared yet,
        or b) a transaction has gone through and the credits haven't been returned to
        the RX component yet.
        """
        self._credits: list[int] = copy(credits)

        """
        This variable indicates the maximum amount of credits the creaditor can give out.
        It's value is constant and equal to value passed in the 'credits' argument.
        If a value of a item is equal to zero, it means that number of credits for this
        specific type of transaction is infinite.
        """
        self._max_credits: list[int] = copy(credits)
        self._states: list[AvstCreditorStatesTX] = [AvstCreditorStatesTX.START_INIT] * self._segments

        self._init_control_signals()
        self._propagate_control_signals()

    def get_credits(self, tlp_type: int) -> int:
        """
        Function for getting number of available credits for the specified type of transaction.
        If maximum number of credits is zero, it means infinite credits and the highest value of
        positive integer is returned.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.

        Returns:
            Number of available credits.
        """
        if self._max_credits[tlp_type] == 0:
            return maxsize*2 + 1
        else:
            return self._max_credits[tlp_type] - self._credits[tlp_type]

    def update_credits(self, tlp_type: int, credits: int) -> None:
        """
        Increments number of credits of specified type available to this creditor
        by number of credits used an inbound transaction.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.
            credits: number of credits used by the transaction.
        """
        self._credits[tlp_type] += credits

    def _init_control_signals(self):
        self._init: Binary = Binary(bits=self._segments)
        self._update: Binary = Binary(bits=self._segments)
        self._update_cnt: BinaryVector = BinaryVector(item_count=self._segments, item_bits=self._data_len)
        self._init_ack: Binary = Binary(bits=self._segments)

    def _propagate_control_signals(self):
        self.bus.init.value = self._init.int
        self.bus.update.value = self._update.int
        self.bus.update_cnt.value = self._update_cnt.int

    def _read_control_signals(self):
        self._init_ack.value = self.bus.init_ack.value.integer

    def _set_update_cnt(self, segment: int, next_state: AvstCreditorStatesTX):
        """
        Sets value of update_cnt signal.

        Args:
            segment: number of segment where whichs signal are to be set.
            next_state: to which state should the FSM transition to after this function
        """

        max_credits_per_trans: int = self._update_cnt[0].maxint

        if self._credits[segment] > 0:
            self._update[segment] = 1

            if self._credits[segment] >= max_credits_per_trans:
                self._update_cnt[segment] = max_credits_per_trans
                self._credits[segment] -= max_credits_per_trans
            else:
                self._update_cnt[segment] = self._credits[segment]
                self._credits[segment] = 0

        else:
            self._update[segment] = 0
            self._states[segment] = next_state

    async def _send_thread(self):
        """
        FSM operating the TX side of R-TILE credit interface.
        """
        states = AvstCreditorStatesTX

        while True:
            await self._clk_re

            for i in range(self._segments):
                match self._states[i]:
                    case states.START_INIT:
                        self._init[i] = 1
                        self._states[i] = states.WAITING_FOR_ACK
                    case states.WAITING_FOR_ACK:
                        self._read_control_signals()
                        self._states[i] = states.DECLARE_CREDITS if self._init_ack[i] else states.WAITING_FOR_ACK
                    case states.DECLARE_CREDITS:
                        self._update[i] = 1
                        self._set_update_cnt(i, states.WAITING_1)
                    case states.WAITING_1:
                        self._states[i] = states.WAITING_2
                    case states.WAITING_2:
                        self._states[i] = states.END_INIT
                    case states.END_INIT:
                        self._init[i] = 0
                        self._states[i] = states.UPDATE_CREDITS
                    case states.UPDATE_CREDITS:
                        self._set_update_cnt(i, states.UPDATE_CREDITS)

            self._propagate_control_signals()


class AvstCreditorRX(BusDriver):
    """Driver controlling the RX side of R-TILE credit interface."""

    _signals = ["init", "update", "update_cnt", "init_ack"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._segments: int = len(self.bus.init)
        self._data_len: int = len(self.bus.update_cnt) // self._segments

        self._credits: list[int] = [0] * self._segments
        self._init_credits: list[int] = [0] * self._segments
        self._states: list[AvstCreditorStatesRX] = [AvstCreditorStatesRX.WAITING_FOR_INIT] * self._segments

        self._init_control_signals()
        self._propagate_control_signals()

    def get_credits(self, tlp_type: int) -> int:
        """
        Function for getting number of available credits for the specified type of transaction.
        If maximum number of credits is zero, it means infinite credits and the highest value of
        positive integer is returned.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.

        Returns:
            Number of available credits.
        """
        if self._init_credits[tlp_type] == 0:
            return maxsize*2 + 1
        else:
            return self._credits[tlp_type]

    def update_credits(self, tlp_type: int, credits: int) -> None:
        """
        Decrements number of credits of specified type available to this creditor
        by number of credits used by an outgoing transaction.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.
            credits: number of credits used by the transaction.
        """
        if self._credits[tlp_type] - credits < 0:
            self._credits[tlp_type] = 0
        else:
            self._credits[tlp_type] -= credits

    def _init_control_signals(self):
        self._init: Binary = Binary(bits=self._segments)
        self._update: Binary = Binary(bits=self._segments)
        self._update_cnt: BinaryVector = BinaryVector(item_count=self._segments, item_bits=self._data_len)
        self._init_ack: Binary = Binary(bits=self._segments)

    def _propagate_control_signals(self):
        self.bus.init_ack.value = self._init_ack.int

    def _read_control_signals(self):
        self._init.value       = self.bus.init.value.integer
        self._update.value     = self.bus.update.value.integer
        self._update_cnt.value = self.bus.update_cnt.value.integer

    async def _send_thread(self):
        """
        FSM operating the RX side of R-TILE credit interface.
        """
        states = AvstCreditorStatesRX

        while True:
            await self._clk_re

            self._read_control_signals()

            for i in range(self._segments):
                match self._states[i]:
                    case states.WAITING_FOR_INIT:
                        if self._init[i]:
                            self._states[i] = states.RESPOND_WITH_ACK
                    case states.RESPOND_WITH_ACK:
                        self._init_ack[i] = 1
                        self._states[i] = states.UPDATE
                    case states.UPDATE:
                        self._init_ack[i] = 0

                        if self._update[i]:
                            self._credits[i] += self._update_cnt[i].int

                            if self._init[i]:
                                self._init_credits[i] += self._update_cnt[i].int

            self._propagate_control_signals()


class AvstCreditRequester(BusDriver):
    """
    Catches components sent by AvstRequester and AvstCompleter and checks, if there
    are enought credits of the specific type to forward them to the AvstPcieDriverMaster.
    If not, they are stopped until there are enough credits. It also updates number
    of credits consumed by a transaction after letting it through.
    """
    def __init__(self, rx_driver: AvstPcieDriverMaster, rx_header_creditor: AvstCreditorRX, rx_data_creditor: AvstCreditorRX, *, params: Optional[dict] = {"min_hcrdt": 0, "min_dcrdt": 32, "bytes_per_crdt": 16}):
        self._signals = rx_driver._signals
        super().__init__(rx_driver.entity, rx_driver.name, rx_driver.clock)
        self.bus = rx_driver.bus

        self._driver: AvstPcieDriverMaster = rx_driver
        self._header_creditor: AvstCreditorRX = rx_header_creditor
        self._data_creditor: AvstCreditorRX = rx_data_creditor
        self._rc_queue: PriorityQueue = PriorityQueue()
        self._cq_queue: PriorityQueue = PriorityQueue()
        self._min_hcrdt = params["min_hcrdt"]
        self._min_dcrdt = params["min_dcrdt"]
        self._bytes_per_credit = params["bytes_per_crdt"]
        self._frame_cnt = 0

    async def write_rc(self, data: dict):
        """
        Catches completion request transaction sent by AvstRequester.
        """
        self._rc_queue.put_nowait((self._frame_cnt, AvstTransactionTypes.Completion, data))
        self._frame_cnt += 1

    async def write_cq(self, data: dict):
        """
        Catches posted and non-poster transaction sent by AvstCompleter.
        """
        header = RequestHeader().deserialize(data["HDR"])
        pcie_trans_type = header.req_t

        if pcie_trans_type in PcieTransactionTypes.MWr:
            avst_trans_type = AvstTransactionTypes.Posted
        elif pcie_trans_type in PcieTransactionTypes.MRd:
            avst_trans_type = AvstTransactionTypes.NonPosted
        else:
            raise NotImplementedError(f"Pcie transaction of type {pcie_trans_type} is not supported.")

        self._cq_queue.put_nowait((self._frame_cnt, avst_trans_type, data))
        self._frame_cnt += 1

    async def _send_thread(self):
        """
        There are two queues - request queue and completion queue. If there is a transaction in the queue,
        the transaction is taken out, it's type is determined and credits are checked. If there aren't enough
        credits of the specific type, transaction is returned to the queue and waits, until there are enough
        credits. Once there are enough credits to send the transaction, number of credits are updated based
        of the length of the transaction and the transaction is sent to the AvstDriverMaster.
        """

        while True:
            await self._clk_re

            for queue, callback in [(self._rc_queue, self._driver.write_rc), (self._cq_queue, self._driver.write_cq)]:
                while (queue.qsize() > 0):
                    priority, trans_type, data = queue.get_nowait()

                    hcrdt = self._header_creditor.get_credits(trans_type.value)
                    dcrdt = self._data_creditor.get_credits(trans_type.value)

                    if (hcrdt > self._min_hcrdt) and (dcrdt > self._min_dcrdt):
                        data_len = (data["DATA"].bit_length() + 7) // 8

                        self._header_creditor.update_credits(trans_type.value, 1)

                        consumed_data_credits = ceildiv(self._bytes_per_credit, data_len)
                        self._data_creditor.update_credits(trans_type.value, consumed_data_credits)

                        await callback(data)

                    else:
                        queue.put_nowait((priority, trans_type, data))
                        break


class AvstCreditReceiver(ProxyMonitor):
    """
    Returns credits to the AvstCreditorTX when a transaction comes through. Also checks, if there are enough
    credits declared to the RX component to send the detected transaction. If not, an exception is raised.
    """
    def __init__(self, monitor: AvstPcieMonitor, tx_header_creditor: AvstCreditorTX, tx_data_creditor: AvstCreditorTX, *, min_hcrdt: int = 0, min_dcrdt: int = 32, bytes_per_credit: int = 16):
        super().__init__(monitor)
        self._header_creditor = tx_header_creditor
        self._data_creditor = tx_data_creditor
        self._min_hcrdt = min_hcrdt
        self._min_dcrdt = min_dcrdt
        self._bytes_per_credit = bytes_per_credit

    def _filter_transaction(self, transaction):
        ct  = AvstTransactionTypes
        ptt = PcieTransactionTypes

        header_bytes, data = transaction

        header = RequestHeader().deserialize(int.from_bytes(header_bytes, 'big'))
        pcie_trans_type = header.req_t

        if pcie_trans_type in ptt.MWr:
            index = ct.Posted.value
        elif pcie_trans_type in ptt.MRd:
            index = ct.NonPosted.value
        elif pcie_trans_type in ptt.CplD:
            index = ct.Completion.value
        else:
            raise NotImplementedError(f"Pcie transaction of type {pcie_trans_type} is not supported.")

        hcrdt = self._header_creditor.get_credits(index)
        dcrdt = self._data_creditor.get_credits(index)

        if hcrdt < self._min_hcrdt or dcrdt < self._min_dcrdt:
            trans_type_str = ["Completion", "Non-posted", "Posted"][index]
            raise RuntimeWarning(f"Transaction of type {trans_type_str} was received even though credits are too low ({hcrdt=}, {dcrdt=}).")

        # giving credits back to creditor
        self._header_creditor.update_credits(index, 1)

        consumed_credits = ceildiv(self._bytes_per_credit, len(data))
        self._data_creditor.update_credits(index, consumed_credits)

        self._recv(transaction)
