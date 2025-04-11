# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. states. p. o.
# Author(states): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.binary import Binary, BinaryVector, BinarySignals
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
        self.__segments: int = len(self.bus.init)
        self.__data_len: int = len(self.bus.update_cnt) // self.__segments

        """
        This variable works a little different then might be expected. It indicates number
        of credits that have been given or returned to this creditor. So if this value is
        equal of zero, it means that all credits have been declared to the RX component.
        Value higher than zero means, that a) not all credits have been declared yet,
        or b) a transaction has gone through and the credits haven't been returned to
        the RX component yet.
        """
        self.__credits: list[int] = copy(credits)

        """
        This variable indicates the maximum amount of credits the creaditor can give out.
        It's value is constant and equal to value passed in the 'credits' argument.
        If a value of a item is equal to zero, it means that number of credits for this
        specific type of transaction is infinite.
        """
        self.__max_credits: list[int] = copy(credits)

        # setting up BinarySignals interface
        self.__signal = BinarySignals(parent=self, params={
            "init_ack": Binary(bits=self.__segments)
        })

        self.__states: list[AvstCreditorStatesTX] = [AvstCreditorStatesTX.START_INIT] * self.__segments

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
        if self.__max_credits[tlp_type] == 0:
            return maxsize*2 + 1
        else:
            return self.__max_credits[tlp_type] - self.__credits[tlp_type]

    def update_credits(self, tlp_type: int, credits: int) -> None:
        """
        Increments number of credits of specified type available to this creditor
        by number of credits used an inbound transaction.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.
            credits: number of credits used by the transaction.
        """
        self.__credits[tlp_type] += credits

    def _init_control_signals(self):
        self.__init: Binary = Binary(bits=self.__segments)
        self.__update: Binary = Binary(bits=self.__segments)
        self.__update_cnt: BinaryVector = BinaryVector(item_count=self.__segments, item_bits=self.__data_len)

    def _clear_control_signals(self):
        self.__init.value = 0
        self.__update.value = 0
        self.__update_cntm_count.value = 0

    def _propagate_control_signals(self):
        self.bus.init.value = self.__init.int
        self.bus.update.value = self.__update.int
        self.bus.update_cnt.value = self.__update_cnt.int

    def _set_update_cnt(self, segment: int, next_state: AvstCreditorStatesTX):
        """
        Sets value of update_cnt signal.

        Args:
            segment: number of segment where whichs signal are to be set.
            next_state: to which state should the FSM transition to after this function
        """

        max_credits_per_trans: int = self.__update_cnt[0].maxint

        if self.__credits[segment] > 0:
            self.__update[segment] = 1

            if self.__credits[segment] >= max_credits_per_trans:
                self.__update_cnt[segment] = max_credits_per_trans
                self.__credits[segment] -= max_credits_per_trans
            else:
                self.__update_cnt[segment] = self.__credits[segment]
                self.__credits[segment] = 0

        else:
            self.__update[segment] = 0
            self.__states[segment] = next_state

    async def _send_thread(self):
        """
        FSM operating the TX side of R-TILE credit interface.
        """
        states = AvstCreditorStatesTX

        while True:
            await self._clk_re

            for i in range(self.__segments):
                match self.__states[i]:
                    case states.START_INIT:
                        self.__init[i] = 1
                        self.__states[i] = states.WAITING_FOR_ACK
                    case states.WAITING_FOR_ACK:
                        self.__states[i] = states.DECLARE_CREDITS if self.__signal.init_ack[i] else states.WAITING_FOR_ACK
                    case states.DECLARE_CREDITS:
                        self.__update[i] = 1
                        self._set_update_cnt(i, states.WAITING_1)
                    case states.WAITING_1:
                        self.__states[i] = states.WAITING_2
                    case states.WAITING_2:
                        self.__states[i] = states.END_INIT
                    case states.END_INIT:
                        self.__init[i] = 0
                        self.__states[i] = states.UPDATE_CREDITS
                    case states.UPDATE_CREDITS:
                        self._set_update_cnt(i, states.UPDATE_CREDITS)

            self._propagate_control_signals()


class AvstCreditorRX(BusDriver):
    """Driver controlling the RX side of R-TILE credit interface."""

    _signals = ["init", "update", "update_cnt", "init_ack"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.__segments: int = len(self.bus.init)
        self.__data_len: int = len(self.bus.update_cnt) // self.__segments

        self.__credits: list[int] = [0] * self.__segments
        self.__init_credits: list[int] = [0] * self.__segments

        self.__signal = BinarySignals(parent=self, params={
            "init"       : Binary(bits=self.__segments),
            "update"     : Binary(bits=self.__segments),
            "update_cnt" : BinaryVector(item_count=self.__segments, item_bits=self.__data_len),
        })

        self.__states: list[AvstCreditorStatesRX] = [AvstCreditorStatesRX.WAITING_FOR_INIT] * self.__segments

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
        if self.__init_credits[tlp_type] == 0:
            return maxsize*2 + 1
        else:
            return self.__credits[tlp_type]

    def update_credits(self, tlp_type: int, credits: int) -> None:
        """
        Decrements number of credits of specified type available to this creditor
        by number of credits used by an outgoing transaction.

        Args:
            tlp_type: type of the transaction. It is advised to use the AvstTransactionTypes enum.
            credits: number of credits used by the transaction.
        """
        if self.__credits[tlp_type] - credits < 0:
            self.__credits[tlp_type] = 0
        else:
            self.__credits[tlp_type] -= credits

    def _init_control_signals(self):
        self.__init_ack: Binary = Binary(bits=self.__segments)

    def _clear_control_signals(self):
        self.__init_ack.value = 0

    def _propagate_control_signals(self):
        self.bus.init_ack.value = self.__init_ack.int

    async def _send_thread(self):
        """
        FSM operating the RX side of R-TILE credit interface.
        """
        states = AvstCreditorStatesRX

        while True:
            await self._clk_re

            for i in range(self.__segments):
                match self.__states[i]:
                    case states.WAITING_FOR_INIT:
                        if self.__signal.init[i]:
                            self.__states[i] = states.RESPOND_WITH_ACK
                    case states.RESPOND_WITH_ACK:
                        self.__init_ack[i] = 1
                        self.__states[i] = states.UPDATE
                    case states.UPDATE:
                        self.__init_ack[i] = 0

                        if self.__signal.update[i]:
                            self.__credits[i] += self.__signal.update_cnt[i].int

                            if self.__signal.init[i]:
                                self.__init_credits[i] += self.__signal.update_cnt[i].int

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

        self.__driver: AvstPcieDriverMaster = rx_driver
        self.__header_creditor: AvstCreditorRX = rx_header_creditor
        self.__data_creditor: AvstCreditorRX = rx_data_creditor
        self.__rc_queue: PriorityQueue = PriorityQueue()
        self.__cq_queue: PriorityQueue = PriorityQueue()
        self.__min_hcrdt = params["min_hcrdt"]
        self.__min_dcrdt = params["min_dcrdt"]
        self.__bytes_per_credit = params["bytes_per_crdt"]
        self.__frame_cnt = 0

    async def write_rc(self, data: dict):
        """
        Catches completion request transaction sent by AvstRequester.
        """
        self.__rc_queue.put_nowait((self.__frame_cnt, AvstTransactionTypes.Completion, data))
        self.__frame_cnt += 1

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

        self.__cq_queue.put_nowait((self.__frame_cnt, avst_trans_type, data))
        self.__frame_cnt += 1

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

            for queue, callback in [(self.__rc_queue, self.__driver.write_rc), (self.__cq_queue, self.__driver.write_cq)]:
                while (queue.qsize() > 0):
                    priority, trans_type, data = queue.get_nowait()

                    hcrdt = self.__header_creditor.get_credits(trans_type.value)
                    dcrdt = self.__data_creditor.get_credits(trans_type.value)

                    if (hcrdt > self.__min_hcrdt) and (dcrdt > self.__min_dcrdt):
                        data_len = (data["DATA"].bit_length() + 7) // 8

                        self.__header_creditor.update_credits(trans_type.value, 1)

                        consumed_data_credits = ceildiv(self.__bytes_per_credit, data_len)
                        self.__data_creditor.update_credits(trans_type.value, consumed_data_credits)

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
        self.__header_creditor = tx_header_creditor
        self.__data_creditor = tx_data_creditor
        self.__min_hcrdt = min_hcrdt
        self.__min_dcrdt = min_dcrdt
        self.__bytes_per_credit = bytes_per_credit

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

        hcrdt = self.__header_creditor.get_credits(index)
        dcrdt = self.__data_creditor.get_credits(index)

        if hcrdt < self.__min_hcrdt or dcrdt < self.__min_dcrdt:
            trans_type_str = ["Completion", "Non-posted", "Posted"][index]
            raise RuntimeWarning(f"Transaction of type {trans_type_str} was received even though credits are too low ({hcrdt=}, {dcrdt=}).")

        # giving credits back to creditor
        self.__header_creditor.update_credits(index, 1)

        consumed_credits = ceildiv(self.__bytes_per_credit, len(data))
        self.__data_creditor.update_credits(index, consumed_credits)

        self._recv(transaction)
