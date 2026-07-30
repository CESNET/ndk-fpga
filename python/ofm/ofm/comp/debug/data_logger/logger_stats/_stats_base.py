# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

from typing import Any

from ._utils import ConvertDefault, FormatDefault


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
        self._data: Any = []

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
