#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger


from ._stats_base import DefaultStat
from ._utils import ConvertTime, FormatDefault, Multipliers


class Counter(DefaultStat):
    """
    Data logger's counter statistics

    Data format: `[x, y, ...]`

    - Data contains counter's value from each load call
    """

    def __init__(self, index : int, *args, **kwargs):
        """
        Parameters
        ----------
            index : int
                Counter index inside data_logger
            name : str
                Statistics name
            logger : DataLogger class
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        super().__init__(*args, **kwargs)
        self.index = index

    def load(self):
        super().load()

        self._raw_data = self.logger.load_cnter(self.index)
        self._data.append(self.convert(self._raw_data))


class TimeCounter(DefaultStat):
    """
    Data logger's statistics for measuring time / latency of some operation

    Data format: `[x, y, ...]`

    - Data contains counter's value from each load call
    """

    def __init__(self, index : int, freq : float, *args, units : str = 's', **kwargs):
        """
        Parameters
        ----------
            index int
                Counter measuring number of clock cycles for which operation occurred
            freq float
                Frequency of the FPGA clocks [HZ]
            name str
                Statistics name
            units str
                Time units ('h', 'min', 's', 'ms', 'us', 'ns')
            logger DataLogger
                DataLogger class
            convert : Callable[[float], float])
                Optional conversion function
            format : Callable[[float], str])
                Optional format function
        """

        if 'format' not in kwargs:
            kwargs['format'] = FormatDefault(units=units, decimal=3)
        super().__init__(*args, **kwargs)
        self.index = index
        self.freq = freq
        self.units = units

    def load(self):
        super().load()

        ticks = self.logger.load_cnter(self.index)
        time_s = ConvertTime(self.freq, units=self.units)(ticks)

        self._raw_data = time_s
        self._data.append(self.convert(self._raw_data))


class FlowCounter(DefaultStat):
    """
    Data logger's statistics for measuring data flow using two counters (number of words and number of ticks)

    Data flow units are: Gb/s

    Data format: `[x, y, ...]`

    - Data contains counter's value from each load call
    """

    def __init__(
            self,
            index_words : int,
            index_ticks : int,
            freq : float,
            word_bits : float = 1,
            units : str = 'Gb/s',
            *args, **kwargs
    ):
        """
        Parameters
        ----------
            index_words : int
                Counter measuring number of data packets
            index_ticks : int
                Counter measuring number of clock cycles during which communication occurred
            freq : float
                Frequency of the FPGA clocks [HZ]
            word_bits : float
                Number of bits inside one data word
            name : str
                Statistics name
            logger : DataLogger
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        if 'format' not in kwargs:
            kwargs['format'] = FormatDefault(units='Gb/s', decimal=3)
        super().__init__(*args, **kwargs)
        self.index_words = index_words
        self.index_ticks = index_ticks
        self.freq = freq
        self.word_bits = word_bits
        self.units = units

    def load(self):
        super().load()

        words = self.logger.load_cnter(self.index_words)
        ticks = self.logger.load_cnter(self.index_ticks)

        self._raw_data = self._convert(words, ticks)
        self._data.append(self.convert(self._raw_data))

    def _convert(self, words, ticks):
        DataUnits = {
            'b': self.word_bits,        # Bits
            'B': self.word_bits / 8,    # Bytes
            'T': 1,                     # Transfers
            'p': 1,                     # Packets
        }

        try:
            if self.units[2] == '/':
                mult    = Multipliers[self.units[0]]
                data    = DataUnits[self.units[1]]
                t       = self.units[3:]
            else:
                mult    = 1
                data    = DataUnits[self.units[0]]
                t       = self.units[2:]
        except KeyError:
            raise Exception(f"Unit {self.units} is not recognized")

        time = ConvertTime(self.freq, units=t)(ticks)
        if time == 0:
            return 0
        if mult == 0:
            return 0

        return words * data / time / mult
