#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

import numpy as np
from typing import List, Callable, Any, Optional

from ._stats_other import Custom


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

        self.stats: list = []
        self.time: list = []

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
