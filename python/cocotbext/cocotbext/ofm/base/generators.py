# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

from random import choices

from .transaction import Transaction, IdleTransaction


class IdleGenerator():
    """
    Idle generator ensures interlacing idle and data transactions in Drivers.

    Idle generators can adopt various behaivour such a "no idles" (full throughput on bus),
    "random idles", "rate limiter", etc.

    This base IdleGenerator generates no idles.

    Driver uses the idle generator by calling pair of .get and .put methods.
    The get method returns a number of idle items, which should be inserted on the bus.
    The put method awaits real number of idle items, which were present on the bus.

    Some idle generators need to know more about the bus parameters and should be parametrized
    with proper configure call.
    """

    def __init__(self):
        # some generators need to be fully configured before the put/get method can be called
        self._cfg_complete = False

    def configure(self, **kwargs):
        pass

    def get(self, transaction: Transaction, *args, **kwargs) -> int:
        """
        return count of items (single IdleTransaction) that should be inserted on bus before next DataTransaction.

        Note that driver doesn't have to follow the returned value.
        Also the handshaked bus can insert dst_rdy=0 states, which doesn't allow to transmit DataTransaction.
        The Generator can handle mismatching items count in put method.

        kwargs can contains optional specifying data:
            'first': int        # first index of item in transaction for partial send
            'last':  int        # last index of item in transaction for partial send
        """
        return 0

    def put(self, transaction: Transaction, *args, **kwargs) -> None:
        """
        Driver calls this function whenever a transaction or its part was sent.

        The IdleGenerator can check for integrity.
        Differences from the planned idles can be logged or an Exception can be raised.

        kwargs can contains optional specifying data:
            'first': int        # first index of item in transaction for partial send
            'last':  int        # last index of item in transaction for partial send
            'items': int        # count of items on bus
            'start': bool       # start of transaction was sent
            'end':   bool       # end of transaction was sent (implies transaction was completly sent)
        """


class EthernetRateLimiter(IdleGenerator):
    """
    Limit throughput to achieve specified maximum rate on Ethernet by generating IdleTransaction.

    Ensure the driver puts transaction with "end" argument.
    """

    def __init__(self, bitrate):
        super().__init__()

        self._bitrate = bitrate
        self._current_rate = 0

        # Add SFD, CRC, IPG; in items units
        self._packet_overhead = 8 + 4 + 12

    def configure(self, **kwargs):
        super().configure(**kwargs)

        #assert bits_per_item == 8
        clk_freq = kwargs.get("clk_freq")
        bits_per_word = kwargs.get("bits_per_word")
        if clk_freq and bits_per_word:
            self._cfg_complete = True

            target_bitrate = self._bitrate / (clk_freq / 1_000_000)
            # The self._target_rate value is percentual load of the bus.
            # For example: 0.23 (23%) means 23 Data items for each 100 items,
            # that is 23:77 data:idle items ratio
            self._target_rate = target_bitrate / bits_per_word

    def get(self, transaction, **kwargs):
        assert self._cfg_complete
        rate = (self._current_rate - self._target_rate) / self._target_rate
        return int(max(0, rate))

    def put(self, transaction, **kwargs):
        assert self._cfg_complete

        items = kwargs['items']
        ir = self._current_rate

        if not isinstance(transaction, IdleTransaction):
            ir += items
            if kwargs.get("end", False):
                ir += self._packet_overhead

        # decrease current rate with the expected target rate to maintain value near zero
        ir -= items * self._target_rate
        self._current_rate = 0 if ir < 0 else ir


class ItemRateLimiter(IdleGenerator):
    """
    Limit throughput to achieve specified rate by generating IdleTransactions.

    Supply the "random_idles" argument to generate IdleTransactions with a grain of randomness.
    If unsupplied or False, IdleTransactions are generated quite periodically (depends on dst_rdy).

    Expects:
        rate_percentage (int): throughput percentage.
                               E.g., rate_percentage=90 means 90% throughput (10% IdleTransactions).
                               When set to 0 (default), IdleTransactions are generated at random.

    Optional (kwargs):
        'random_idles'      (bool): Return the number of IdleTransactions with a grain of randomness, yet still trying to preserve the ratio.
                                    If unsupplied or False, IdleTransactions are generated quite periodically (dependant on dst_rdy).
                                    Irrelevant when `rate_percentage` is set to 0 (=IdleTransactions are generated at random).
        'max_idles'         (int):  Maximum number of IdleTransactions that can be returned by the `get` method.
                                    Used only when `rate_percentage` is set to 0 (=IdleTransactions are generated at random).
        'zero_idles_chance' (int):  Probability of the `get` method returning 0 IdleTransactions compared to all other values.
                                    This is to reduce the number of IdleTransactions.
                                    Expected values are between (inclusive) 0 and 100 (100 results in full-speed).
                                    When `max_idles` is set to 0, `zero_idles_chance` is automatically set to 100.
                                    Used only when `rate_percentage` is set to 0 (=IdleTransactions are generated at random).
    """

    def __init__(self, rate_percentage=0, **kwargs):
        super().__init__()

        self._rate_percentage = rate_percentage
        self._idles_random = kwargs.get("random_idles", True)
        self._max_idles = kwargs.get("max_idles", 5)
        self._zero_idles_chance = kwargs.get("zero_idles_chance", 50)

        self._target_rate_ratio = self._rate_percentage / 100
        self._idle_rate_ratio = 1 - self._target_rate_ratio
        self._idle_transactions = 0
        self._total_transactions = 0

    def configure(self, **kwargs):
        super().configure(**kwargs)

        self._rate_percentage = kwargs.get("rate_percentage", self._rate_percentage)
        self._idles_random = kwargs.get("random_idles", self._idles_random)
        self._max_idles = kwargs.get("max_idles", self._max_idles)
        self._zero_idles_chance = kwargs.get("zero_idles_chance", self._zero_idles_chance)
        if self._max_idles == 0:
            self._zero_idles_chance = 100

    def get(self, transaction, **kwargs):

        # Return random number of Idle transactions (=random throughput)
        if self._rate_percentage == 0:
            # The number of Idle transactions is in range (0, self._max_idles)
            # with 100-self._zero_idles_chance % chance of returning 0.
            idles = [i for i in range(0, self._max_idles)]
            wghts = [(100 - self._zero_idles_chance) // max(len(idles), 1)] * len(idles)
            return choices(population=[0, *idles], weights=[self._zero_idles_chance, *wghts], k=1)[0]

        ## Calculate the amount of Idle Transactions to uphold the set ratio (throughput)
        # The basic formula:
        # self._idle_rate_ratio = self._idle_transactions / self._total_transactions
        # When sending (using the put function) non-idle transactions,
        # self._total_transactions increments and I need to find value x, which
        # represents the number of idle transactions to send to preserve the set ratio.
        # Hence:
        # self._idle_rate_ratio = (self._idle_transactions + x) / self._total_transactions
        # Find the value of x (+truncate) like so:
        x = int(self._idle_rate_ratio * self._total_transactions - self._idle_transactions)
        if self._idles_random:
            if x < 0:
                return 0
            else:
                # This allows to return +1 more than is actually calculated.
                return choices(population=range(x+2), weights=None, k=1)[0]
        else:
            return max(0, x)

    def put(self, transaction, **kwargs):
        items_count = kwargs.get("items", 1)

        if isinstance(transaction, IdleTransaction):
            self._idle_transactions += items_count

        self._total_transactions += items_count
