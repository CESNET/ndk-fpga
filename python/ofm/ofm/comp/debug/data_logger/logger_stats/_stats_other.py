#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

import json

from ._stats_base import DefaultStat
from ._utils import FormatDefault


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

        if "format" not in kwargs:
            kwargs["format"] = format
        super().__init__(*args, **kwargs)
        self.index = index

        self._raw_data = None
        self._data = None

    def load(self):
        super().load()

        ctrli = self.logger.load_ctrl(0)
        data = self.logger.get_bits(ctrli, self.logger.mi_width, self.logger.mi_width * self.index)

        self._raw_data = data
        self._data = self.convert(self._raw_data)


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
