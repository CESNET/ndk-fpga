# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for structured loading and saving statistics from data_logger

import numpy as np
import pandas as pd
from typing import List, Callable, Any

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
