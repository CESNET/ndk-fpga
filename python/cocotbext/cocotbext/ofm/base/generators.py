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
