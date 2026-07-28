# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

import numpy as np
from typing import List

from ._stats_base import DefaultStat
from ._base import LoggerStats
from ._utils import FormatDefaultValue


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

        if "format" not in kwargs:
            kwargs["format"] = format
        super().__init__(*args, **kwargs)
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

        if "format" not in kwargs:
            kwargs["format"] = format
        super().__init__(*args, **kwargs)
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
