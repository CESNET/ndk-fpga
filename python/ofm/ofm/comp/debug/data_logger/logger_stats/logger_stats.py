#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

import json
import numpy as np
import pandas as pd
from typing import List, Callable, Any, Optional


# Common conversion functions #

Multipliers = {
    'k': 10**3,
    'M': 10**6,
    'G': 10**9,
    'T': 10**12,
}


TimeUnits = {
    'd':    24 * 3600,
    'h':    3600,
    'min':  60,
    's':    1,
    'ms':   1 / 10**3,
    'us':   1 / 10**6,
    'ns':   1 / 10**9,
}


def ConvertDefault(v):
    return v


def ConvertTime(freq : float, units : str = "ns") -> Callable[[float], float]:
    """
    Convert numeric value to time [ns] with specified CLK frequency [Hz]

    Parameters
    ----------
        freq : float
            Frequency of the FPGA clocks [HZ]
        units : str
            In which units should be time returned ('h', 'min', 's', 'ms', 'us', 'ns')

    Returns
    -------
        Callable [[float], float]
            Conversion function
    """

    if units not in TimeUnits:
        raise Exception(f"Unit {units} is not recognized")
    else:
        mult = 1 / TimeUnits[units]

    def res(v):
        return v / freq * mult

    return res


def ConvertStates(states : List[Any]) -> Callable[[float], Any]:
    """
    Convert numeric value to discrete states (for example strings)

    Parameters
    ----------
        states : List[Any]
            Value 'i' will be converted to item at list's i-th index

    Returns
    -------
        Callable[[float], Any]
            Conversion function
    """

    def res(val):
        assert 0 <= val, f"Negative value {val} cannot be converted to state!"
        if val < len(states):
            return states[int(val)]
        else:
            return str(val)

    return res


# Common format functions #

def FormatDefault(
        units : str = '',
        decimal : int = 0,
        only_last : bool = False
) -> Callable[[Any], str]:
    """
    Default formatting function for single valued statistics (for example counter interface)

    Parameters
    ----------
        units : str
            Custom units string that will be appended at the end of statistic
        decimal : int
            Number of decimal places for printing
        only_last : bool
            Print only the latest measurement (else print sum of the measurements)

    Returns
    -------
        Callable[[Any], Str]
            Conversion function
    """

    def res(v):
        if v is None:
            return "-"

        if isinstance(v, (list, pd.core.series.Series, np.ndarray)):
            if only_last or not isinstance(v, (int, float)):
                v = v[-1]
            else:
                v = sum(v)

        unit_str = f" {units}" if len(units) > 0 else ''
        if isinstance(v, (int, float)):
            val_str = f"{v:.{decimal}f}"
        else:
            val_str = str(v)

        return f"{val_str}{unit_str}"

    return res


def FormatDefaultValue(
        format : Callable[[Any], str] = FormatDefault(),
        units : str = ""
) -> Callable[[Any], str]:
    """
    Default formatting function for value interface

    Parameters
    ----------
        format : Callable[[Any], str]
            Formatting function for min, max, avg statistics
        units : str
            Custom units string that will be appended at the end of statistic

    Returns
    -------
        Callable[[Any], Str]
            Conversion function
    """

    return lambda data: f"<{format(data['min'])} / {format(data['avg'])} / {format(data['max'])}> {units}"


class LoggerStats:
    """
    Class for structured loading and printing data_logger statistics

    - Multiple data_loggers can be observed
    - Statistics can be organized in tree structure (using nested LoggerStats classes)
    - Custom names and conversion / format functions can be provided

    Default statistics types:
    - `Constant(index, name)`
    - `Counter(index, name)`
    - `TimeCounter(index, freq, name)` - counter measuring time / latency
    - `FlowTimeCounter(index_words, index_ticks, freq, word_bits, name)` - 2 counters measuring data flow
    - `Value(index, name)`
    - `ValueCMD(index, name, cmd_width, cmds)` - same as Value, but histogram is split to `2**cmd_width` types specified by MSB bits
    - `Custom(name, data)` - statistic's value will be specified during creation or during loading
    - `CustomJSON(name)` - statistic's value will be specified externally by JSON string

    Providing data_logger classes:

    - Data_loggers can be provided to each leaf node manualy
    - Providing data_logger to parent node will copy logger to all sub-nodes
    - Loggers provided in leaf nodes won't be overridden by setting parent node's logger

    Example:

        ```
        stats_a = LoggerStats('Stats A', logger=logger_a)
        stats_b = LoggerStats('Stats B', logger=logger_b)

        stats = LoggerStats('Root stats')
        stats.add_stat(stats_a)
        stats.add_stat(stats_b)

        stats_a.add_stat(Value(7,  'Name A')
        stats_a.add_stat(Value(42, 'Name B', convert=ConvertTime(FREQ)
        ...

        stats.add_stats(
            name='Stats C',
            names=C_names,
            indexes=list(range(7)),
            constructor=lambda i, n: Stats.Counter(i, n)
        )
        ...

        stats.load()
        print(stats.to_str())
        stats.save('stats.npz')
        ```
    """

    StrOffset = 2

    def __init__(self, name : str, logger=None):
        """
        Initialize statistics node (root node or sub-node)

        Parameters
        ----------
            name : str
                Node name
            logger : DataLogger class
                Default data_logger for all sub-statistics in this node
        """

        self.name = name
        self.logger = logger

        self.stats = []
        self.time = []

        def calc_stats(data):
            return data

        self.calc_stats = calc_stats

    def add_stat(self, stat):
        """
        Add new statistic under this node.
        Nested node can be created by passing LoggerStats class.
        """

        stat.set_logger(self.logger)
        self.stats.append(stat)

    def add_stats(
            self,
            indexes : List[int],
            names : List[str],
            constructor : Callable[[int, str], Any],
            name : Optional[str] = None,
            logger=None
    ):
        """
        Add list of the new statistics.
        If name is None (by default), statistics will be added to the current node.
        Otherwise subnode with a given name will be created.

        Example:

            reqs = ['wr req cnt', 'wr req words', ...]
            stats.add_stats(
                name='Requests',
                names=reqs,
                indexes=list(range(len(reqs))),
                constructor=lambda i, n: Stats.Counter(i, n)
            )
        """

        if name is not None:
            group = LoggerStats(name, logger)
            self.add_stat(group)
        else:
            group = self

        for i, name in zip(indexes, names):
            group.add_stat(constructor(i, name))

    def add_calc_stats(self, calc_stats):
        """
        Add callback that will transform statistics after each logging

        Parameters
        ----------
            calc_stats : Callable[[data], data]
                Callback
        """

        self.calc_stats = calc_stats

    def set_logger(self, logger):
        """
        Set default data_logger for this node
        """

        if self.logger is None:
            self.logger = logger

        for s in self.stats:
            s.set_logger(logger)

    def load(self, time : Optional[float] = None):
        """
        Load statistics

        All the statistics except Constant keep the full history of all load calls

        Parameters
        ----------
            time : float
                If specified, new statistic with logging time will be added ('Log time')
        """

        if time is not None:
            self.time.append(time)

        for s in self.stats:
            s.load()

        self.set_data(self.calc_stats(self.data()))

    def data(self):
        """
        Get all statistics from this node

        Data format: `{sub-stat-name: sub-stat-data, ...}`
        """

        res = {s.name: s.data() for s in self.stats}
        if len(self.time) > 0:
            res['Log time'] = self.time
        return res

    def set_data(self, data):
        """
        Set all statistics to new values
        """

        for s in self.stats:
            s.set_data(data[s.name])

        # Add new statistics
        stat_names = map(lambda s: s.name, self.stats)
        for key in data:
            if key not in stat_names:
                self.add_stat(Custom(name=key, data=data[key]))

        if 'Log time' in data:
            self.time = data['Log time']

    def __getitem__(self, key):
        return self.data()[key]

    def __setitem__(self, key, value):
        data = self.data()
        data[key] = value
        self.set_data(data)

    def to_str(self, prefix_len=None, offset=0):
        """
        Get all statistics in string format
        """

        if prefix_len is None:
            prefix_len = self._prefix_len()

        res = [f"{' ' * offset}{self.name}:\n"]
        res += map(lambda s: s.to_str(prefix_len, offset + self.StrOffset), self.stats)
        return ''.join(res) + '\n'

    def _prefix_len(self):
        if len(self.stats) == 0:
            return self.StrOffset
        else:
            return max(map(lambda s: s._prefix_len(), self.stats)) + self.StrOffset

    def save(self, file):
        """
        Save all statistics in compressed numpy format (.npz)
        """

        data = self.data()
        np.savez_compressed(file, np.array(data, dtype=object))

    def load_file(self, file):
        """
        Load all statistics from .npz file
        """

        data = np.load(file, allow_pickle=True)['arr_0'].item()
        self.set_data(data)


class DefaultStat:
    def __init__(
            self,
            name : str,
            logger=None,
            convert=ConvertDefault,
            format=FormatDefault()
    ):
        """
        Parameters
        ----------
            index : int
                Constant position inside data_logger statistic port
            name : str
                Statistics name
            logger : DataLogger class
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        self.name = name
        self.logger = logger
        self.convert = convert
        self.format = format

        self._raw_data = None
        self._data = []

    def set_logger(self, logger):
        if self.logger is None:
            self.logger = logger

    def data(self):
        return self._data

    def set_data(self, data):
        self._data = data

    def to_str(self, prefix=40, offset=0):
        spaces = prefix - len(self.name) - offset
        return f"{' ' * offset}{self.name}{' ' * spaces}: {self.format(self._data)}\n"

    def _prefix_len(self):
        return len(self.name)

    def load(self):
        assert self.logger is not None, f"Data Logger needs to be specified for stat {self.name}"


class Constant(DefaultStat):
    """
    Constant provided in data_logger's CTRLI port

    Assumes that each constant have width of MI_DATA_WIDTH!

    Data format: `x`

    - Data contains constant value from latest call of the load function
    """

    def __init__(self, index : int, *args, **kwargs):
        """
        Parameters
        ----------
            index : int
                Constant position inside data_logger CTRLI port
            name : str
                Statistics name
            logger : DataLogger class
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        super().__init__(*args, format=format, **kwargs)
        self.index = index

        self._raw_data = None
        self._data = None

    def load(self):
        super().load()

        ctrli = self.logger.load_ctrl(0)
        data = self.logger.get_bits(ctrli, self.logger.mi_width, self.logger.mi_width * self.index)

        self._raw_data = data
        self._data = self.convert(self._raw_data)


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


class Value(DefaultStat):
    """
    Data logger's value statistics

    Data format:

        ```
        {
            'min': [x, y, ...],
            'max': [x, y, ...],
            'avg': [x, y, ...],
            'hist': "np.array with shape: (time, boxes)",
            'hist_x': "list with values corresponding to the middles of each histogram box"
        }
        ```
    """

    def __init__(self, index : int, *args, format=FormatDefaultValue(), **kwargs):
        """
        Parameters
        ----------
            index : int
                Value interface index
            name : str
                Statistics name
            logger : DataLogger
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        super().__init__(*args, format=format, **kwargs)
        self.index = index
        self._data = {
            'min': [],
            'avg': [],
            'max': [],
            'hist': None,
            'hist_x': None
        }

    def load(self):
        super().load()

        self._raw_data          = self.logger.load_value(self.index)

        self.width              = self.logger.config["VALUE_WIDTH"][self.index]
        self.value_en           = self.logger.config["VALUE_EN"][self.index]
        self.sum_extra_width    = self.logger.config["SUM_EXTRA_WIDTH"][self.index]
        self.hist_box_cnt       = self.logger.config["HIST_BOX_CNT"][self.index]
        self.hist_box_width     = self.logger.config["HIST_BOX_WIDTH"][self.index]
        self.hist_step          = self.logger.config["HIST_STEP"][self.index]

        metrics = ['min', 'avg', 'max', 'hist']
        ens = ['MIN', 'SUM', 'MAX', 'HIST']
        for m, en in zip(metrics, ens):
            if not self.value_en[en]:
                continue

            if m == 'hist':
                x = [self.convert((i + 0.5) * self.hist_step) for i in range(0, self.hist_box_cnt)]
                y = np.array([self._raw_data['hist']])

                self._data['hist_x'] = x

                if self._data['hist'] is None:
                    self._data['hist'] = y
                else:
                    self._data['hist'] = np.append(self._data['hist'], y, axis=0)
            else:
                self._data[m].append(self.convert(self._raw_data[m]))


class ValueCMD(DefaultStat):
    """
    Same as value statistics, but splits each histogram box to `2 ** cmd_width` measurements (commands).

    Data format:

        ```
        {
            'cmd_0': { ... same as Value ... },
            'cmd_1': { ... same as Value ... },
            ...
        }
        ```
    """

    def __init__(
            self,
            index : int,
            *args,
            cmd_width : int,
            cmds : List[str],
            format=FormatDefaultValue(),
            **kwargs
    ):
        """
        Parameters
        ----------
            index : int
                Value interface index
            name : str
                Statistics name
            cmd_width : int
                MSB bits in data_loggers value statistics represent different commands
            cmds : List[str]
                 The list with commands names
            logger : DataLogger
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        super().__init__(*args, format=format, **kwargs)
        self.index = index

        self.cmd_width = cmd_width
        self.cmds = cmds

        self._data = {}
        for cmd in self.cmds:
            self._data[cmd] = {
                'min': [],
                'avg': [],
                'max': [],
                'hist': None,
                'hist_x': None
            }

    def to_str(self, prefix=40, offset=0):
        spaces = prefix - len(self.name) - offset
        res = f"{' ' * offset}{self.name}:\n"

        for cmd in self.cmds:
            spaces = prefix - len(cmd) - offset - LoggerStats.StrOffset
            res += f"{' ' * (offset + LoggerStats.StrOffset)}{cmd}{' ' * (spaces)}: "
            res += f"{self.format(self._data[cmd])}\n"

        return res

    def _prefix_len(self):
        return max(len(self.name), *list(map(lambda x: len(x), self.cmds))) + LoggerStats.StrOffset

    def load(self):
        super().load()

        self._raw_data = self.logger.load_value(self.index)

        self.width              = self.logger.config["VALUE_WIDTH"][self.index]
        self.value_en           = self.logger.config["VALUE_EN"][self.index]
        self.sum_extra_width    = self.logger.config["SUM_EXTRA_WIDTH"][self.index]
        self.hist_box_cnt       = self.logger.config["HIST_BOX_CNT"][self.index]
        self.hist_box_width     = self.logger.config["HIST_BOX_WIDTH"][self.index]
        self.hist_step          = self.logger.config["HIST_STEP"][self.index]

        self.hist_box_cnt       //= 2 ** self.cmd_width

        x = [self.convert((i + 0.5) * self.hist_step) for i in range(0, self.hist_box_cnt)]

        for i, cmd in enumerate(self.cmds):
            if not self.value_en['HIST']:
                continue

            y = self._raw_data['hist'][i * self.hist_box_cnt : (i + 1) * self.hist_box_cnt]
            y = np.array(y)

            if self._data[cmd]['hist'] is None:
                self._data[cmd]['hist'] = y
            else:
                self._data[cmd]['hist'] = np.append(self._data[cmd]['hist'], y, axis=0)

            self._data[cmd]['hist_x'] = x

            y = np.array(y)
            # Indexes of the non zero items
            non_zero = np.nonzero(y)[0]

            if len(non_zero) == 0:
                min = 0
                max = 0
                avg = 0
            else:
                min = x[non_zero[0]]
                max = x[non_zero[-1]]
                avg = np.dot(x, y) / np.sum(y)

            self._data[cmd]['min'].append(min)
            self._data[cmd]['max'].append(max)
            self._data[cmd]['avg'].append(avg)


class Custom(DefaultStat):
    """
    Statistic with externally specified value (using python object)

    Value can be specified during construction and during load
    """

    def __init__(self, *args, data=None, **kwargs):
        """
        Parameters
        ----------
            name : str
                Statistics name
            data : object
                Statistic data
            logger : DataLogger
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        if 'format' not in kwargs:
            kwargs['format'] = FormatDefault(only_last=True)
        super().__init__(*args, **kwargs)
        self._data = [data]

    def load(self, data=None):
        if data is not None:
            self._data.append(data)


class CustomJSON(Custom):
    """
    Statistic with externally specified value (using JSON string)

    Value can be specified during construction and during load
    """

    def __init__(self, *args, data=None, **kwargs):
        """
        Parameters
        ----------
            name : str
                Statistics name
            data : object
                Statistic data
            logger : DataLogger
                DataLogger class
            convert : Callable[[float], float]
                Optional conversion function
            format : Callable[[float], str]
                Optional format function
        """

        super().__init__(*args, **kwargs)
        if data is None:
            self._data = []
        else:
            self._data = [json.loads(data)]

    def load(self, data=None):
        if data is not None:
            data = json.loads(data)
            self._data.append(data)
