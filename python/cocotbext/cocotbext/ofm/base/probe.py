# throughput_probe.py: Universal probe for measuring throughput and efficiency
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.triggers import RisingEdge
from cocotb.log import SimLog
from cocotb.utils import get_sim_time
from cocotbext.ofm.utils.units import convert_units
from abc import ABC, abstractmethod
from typing import Any


class ProbeInterface:
    """
    Generic class for translating attributes of monitors to probe attributes.

    Atributes:
        interface_dict(dict): keys are names of parameters that the probe wants to retrieve and items are tuples,
                              where the first item is the conversion function and second is tuple with arguments
                              for the convertion function.
        _monitor(BusMonitor): monitor object including the attributes required for probing
    """
    interface_dict = {}

    def __init__(self, monitor):
        self._monitor = monitor

    def __getattr__(self, name: str) -> Any:
        return getattr(self._monitor, self.interface_dict.get(name, None))


class Probe(ABC):
    """
    Generic probe class used for probing specific parameters of simulated component.

    Note: this class by itself does nothing. It is a generic class made to be derived from for specific usages.

    Atributes:
        _interface: child of ProbeInterface.
        _clk_re: Rising edge of cocotb clock.
        _log_intervals(list): list of time intervals, in which is the probe to be active. Time interval is a list
                              in format [start_time, stop_time, units, interval_processed(bool)].
        _period(int): time between logs during every interval in _log_intervals. If set to 0, only one log is
                      printed out at the end of the time interval.
        _units(str): general units to be used in the class.
        _thread: cocotb thread for running the persistant probing function.
    """
    def __init__(self, interface: ProbeInterface, period: int = 0, time_units: str = "us", log_intervals: list = [], callback=None) -> None:
        self._interface = interface
        self._clk_re = RisingEdge(self._interface.clock)
        self._log_intervals = log_intervals
        self._period = period
        self._time_units = time_units

        if not hasattr(self, "log"):
            self.log = SimLog("cocotb.probe.%s" % (self.__class__.__name__))

        if callback is not None:
            self.add_callback(callback)

        self._thread = cocotb.scheduler.add(self._start_probe())

    @abstractmethod
    async def _start_probe(self) -> None:
        """Persistently running function defining the behavior of the probe. Has to be implemented in every child."""
        pass

    def add_log_interval(self, start_time: int, stop_time: int, units: str = "us") -> None:
        """
        Adds a interval, where the probe will do it's duties.

        Args:
            start_time: when the interval should start. If period is used, this time is usually exluded,
                        because it's where the counting starts. So first log is at start_time + period.
            stop_time: time, when the interval should stop. If None, interval ends with the end of the simulation.
            units: units of the start_time and stop_time. Microseconds by default.
        """
        interval = [start_time, stop_time, units, False]

        if stop_time is not None:
            assert stop_time > start_time

        if self._interval_overlaps_log_intervals(interval):
            raise RuntimeError(f"Interval [{start_time},{stop_time},{units}] can't be added, because it overlaps with existing interval.")

        self._log_intervals.append(interval)
        self._log_intervals.sort()

    def clear_log_intervals(self) -> None:
        """Clears logging intervals"""
        self._log_intervals.clear()

    def set_log_period(self, period: int, units: str = "us") -> None:
        """
        Sets period after which are logs to be printed out when in logging interval.

        Args:
            period: period to be set.
            units: units of the period. Microseconds by default.
        """
        self._period = period
        self._time_units = units

    def start_log(self) -> None:
        """Manually start logging interval."""
        if self._simtime_is_in_log_interval():
            raise RuntimeError("Can't start a new log, because the previous one wasn't ended yet.")

        self.add_log_interval(get_sim_time("step"), None, units=self._get_step_units())

    def stop_log(self) -> None:
        """Manually end logging interval."""
        self._log_intervals[0][1] = get_sim_time("step") + 1

    def _get_step_units(self) -> str:
        """Get units of step."""
        for unit in ["fs", "ps", "ns", "us", "ms", "sec"]:
            if get_sim_time(units="step") // int(get_sim_time(units=unit)) == 1:
                return unit

    def _format_units_for_get_sim_time(self, time_units: str) -> str:
        """
        Coverts passed time units to a format used by get_sim_time. So basically only converts 's' to 'sec',
        else just returns the passed units.
        """
        return {"s": "sec"}.get(time_units, time_units)

    def _simtime_is_in_log_interval(self) -> bool:
        """
        Checks if the simulation time is in one of the defined intervals.

        Returns:
            True if in interval, False if not.
        """
        start_time, stop_time = 0, 0
        units, gst_units = "us", "us"
        defaults = True

        for _ in range(len(self._log_intervals)):
            start_time, stop_time, units, end_registered = self._log_intervals[0]
            gst_units = self._format_units_for_get_sim_time(units)
            defaults = False

            if stop_time is None:
                break

            if get_sim_time(units=gst_units) > stop_time:
                if not end_registered:
                    self._log_intervals[0][3] = True
                    return True
                else:
                    del self._log_intervals[0]
            else:
                break

        if not defaults:
            if get_sim_time(units=gst_units) >= start_time:
                if stop_time is None:
                    return True

                if get_sim_time(units=gst_units) <= stop_time:
                    return True

        return False

    def _interval_overlaps_log_intervals(self, interval: list) -> bool:
        """
        Checks if passed interval overlaps with one of the intevals in _log_intervals.

        Args:
            interval: inteval to be checked for overlaps with existing intervals.

        Returns:
            True if interval overlaps, False if not.
        """
        start_time, stop_time, units, _ = interval

        for ei_start_time, ei_stop_time, ei_units, _ in self._log_intervals:
            ei_start_time = convert_units(ei_start_time, ei_units.strip("s"), units.strip("s"))[0]

            if ei_stop_time is None:
                if stop_time is None:
                    return True

                elif (start_time >= ei_start_time) or (stop_time > ei_start_time):
                    return True

            else:
                ei_stop_time = convert_units(ei_stop_time, ei_units.strip("s"), units.strip("s"))[0]

                if stop_time is None:
                    if (start_time >= ei_start_time and start_time < ei_stop_time):
                        return True

                else:
                    start_time_is_in_interval = start_time >= ei_start_time and start_time < ei_stop_time
                    stop_time_is_in_interval = stop_time > ei_start_time and stop_time <= ei_stop_time

                    if start_time_is_in_interval or stop_time_is_in_interval:
                        return True

        return False

    def _get_log_period(self) -> int:
        """
        Returns set period. If no period is set, it is the length of the closest interval. Returns 0 if the
        sim time is not in interval, the interval lasts until the end of the simulation, or no interval is set.
        """
        if self._period == 0:
            try:
                start_time, stop_time, units, _ = self._log_intervals[0]

            except IndexError:
                return 0

            gst_units = self._format_units_for_get_sim_time(units)

            if stop_time is None:
                return 0

            if get_sim_time(units=gst_units) < start_time:
                return 0

            start_time = convert_units(start_time, units.strip("s"), self._time_units.strip("s"))[0]
            stop_time = convert_units(stop_time, units.strip("s"), self._time_units.strip("s"))[0]
            return stop_time - start_time

        return self._period
