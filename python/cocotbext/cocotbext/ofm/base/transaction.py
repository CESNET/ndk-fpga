class BaseTransaction():
    """Base class for transactions"""


class IdleTransaction(BaseTransaction):
    """
    Transaction represents general bus idling

    There is no exact size of IdleTransaction, it should represent the
    smallest unit of data that the bus can transfer. For example,
    one byte on the MFB bus, one item on the MVB bus, one word (clock cycle) on
    common buses.
    """


class Transaction(BaseTransaction):
    """Transactions with real data to be written into bus"""


DataTransaction = Transaction
