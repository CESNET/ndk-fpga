# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import random
from dataclasses import asdict
from cocotb_bus.drivers import BusDriver
from cocotbext.ofm.base.transaction import Transaction
from typing import Callable
from cocotbext.ofm.utils.math import ceildiv


def random_byte():
    """
    Random byte generator
    """
    while True:
        yield random.randrange(256)


def random_bytes(bytes_count: int, generator):
    """
    Generate N random bytes from *generator*
    """
    return bytes(next(generator) for i in range(bytes_count))


def random_packets(min_size=4, max_size=64, count=10):
    """
    Generate N random packets with random length of bytes in min/max range
    """
    for i in range(count):
        yield random_bytes(random.randint(min_size, max_size), random_byte())


def random_integers(mini=0, maxi=100, count=10):
    """
    Generate N random integers inbetween the min/max range
    """
    for i in range(count):
        yield random.randint(mini, maxi)


def random_transactions(trans_type: Transaction, driver: BusDriver, data_sig_name: str, min_size: int = 1, max_size: int = 16,
                        count: int = 10, patterns: dict[list[Callable, list]] = {}):
    """
    Generates N random transactions based on the transaction type and the driver that is going to be used to send
    the transaction. The driver object is used for getting the bit width of the signals that are set by the
    transaction. The name of the data signal also needs to be specified, all other signals will be treated as auxiliaries.
    Length of the transaction is random and between the specified min and max byte count. The value of every word is random
    by default. This can be changed by the 'patterns' parameter, which accepts dictonary that has items of the following
    format: n: (f, a), where 'n' is the name of the signal, 'f' is a function that is used to set the value of each word and
    'a' is a list of arguments that is given to the function as *args.

    Args:
        trans_type: type of the transaction. The type should be a class derived from
                    cocotbext.ofm.base.transaction.Transaction.
        driver: driver that is going to be used to send the transaction.
        min_size: minimum length of the transaction in bytes.
        max_size: maximum length of the transaction in bytes.
        count: number of packets to be generated.
        patterns: dictionary specifying the functions used to set the value of a signal.
    """

    if not hasattr(trans_type(), data_sig_name):
        raise NameError("Passed transaction type does not have the specified data signal in random_transactions.")

    if not hasattr(driver.bus, data_sig_name):
        raise NameError("Passed driver does not have the specified data signal in random_transactions.")

    for _ in range(count):
        transaction   = trans_type()
        data_byte_cnt = random.randint(min_size, max_size)
        data_width    = len(getattr(driver.bus, data_sig_name)) // 8
        trans_cnt     = ceildiv(data_width, data_byte_cnt)

        for name, value in asdict(transaction).items():
            if not hasattr(driver.bus, name):
                continue

            width = len(getattr(driver.bus, name)) if len(getattr(driver.bus, name)) < 8 else 8

            if isinstance(value, int):
                function = random.randint
                args = [0, 2**width-1]
                val = 0
            elif isinstance(value, bytes):
                function = random.randbytes
                args = [1]
                val = b''
            else:
                raise TypeError(f"Value of {name} of type {type(value)} in transaction passed to random_transactions is not supported.")

            if name in patterns.keys():
                function, args = patterns.get(name)

            if name == data_sig_name:
                byte_cnt = data_byte_cnt
            else:
                byte_cnt = trans_cnt * ceildiv(8, len(getattr(driver.bus, name)))

            for _ in range(byte_cnt):
                new_val = function(*args)

                if isinstance(new_val, int):
                    val = (val << width) + new_val
                elif isinstance(new_val, bytes):
                    val += new_val
                else:
                    raise TypeError(f"Unsupported type {type(value)} returned by pattern function passed to random_transactions.")

            setattr(transaction, name, val)

        yield transaction
