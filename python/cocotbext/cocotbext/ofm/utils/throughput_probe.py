# throughput_probe.py: Universal probe for measuring throughput and efficiency
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.base.probe import Probe, ProbeInterface
from cocotb.utils import get_sim_time
from cocotbext.ofm.utils.units import convert_units
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mfb.monitors import MFBMonitor


class ThroughputProbeInterface(ProbeInterface):
    """
    Base class for interfacing between throughput probe and BusMonitor object. By itself does nothing,
    it should be used as a template (to see which attributes throughput probe requires in the interface_dict).
    """
    interface_dict = {
        "clock"     : None,
        "in_reset"  : None,
        "items"     : None,
        "item_width": None,
        "item_cnt"  : None
    }


class ThroughputProbeMvbInterface(ThroughputProbeInterface):
    """Throughput probe interface for the MVB monitor."""
    interface_dict = {
        "clock"     : "clock",
        "in_reset"  : "in_reset",
        "items"     : "_items",
        "item_width": "_item_width",
        "item_cnt"  : "item_cnt"
    }

    def __init__(self, monitor: MVBMonitor):
        super().__init__(monitor)


class ThroughputProbeMfbInterface(ThroughputProbeInterface):
    """Throughput probe interface for the MFB monitor."""
    interface_dict = {
        "clock"     : "clock",
        "in_reset"  : "in_reset",
        "items"     : None,
        "item_width": "_item_width",
        "item_cnt"  : "item_cnt"
    }

    def __init__(self, monitor: MFBMonitor):
        super().__init__(monitor)

    @property
    def items(self):
        return self._monitor._regions * self._monitor._region_items


class ThroughputProbe(Probe):
    """
    Probe for measuring and logging throughput and efficiency.

    Atributes:
        _total_item_cnt(int): total number of items that could've passed through the bus during the simulation.
        _log_vals_cleared(bool): if the values of variables necessary for calculating immediate throughput are
                                 valid or cleared.
        _start_of_period(int): time in the simulation when the measured period started (used for measuring immediate
                               throughput and efficiency).
        _total_item_cnt_at_start_of_period(int): number of total items at the start of the measured period
                                                 (used for measuring immediate throughput and efficiency).
        _vld_item_cnt_at_start_of_period(int): number of valid items at the start of the measured period
                                               (used for measuring immediate throughput and efficiency).

    Usage:
        - A custom interface for the probed bus is necessary for the probe to function. Use one intended for the probed
          bus, or create a new one if it doesn't exist. The interface is basically a conversion layer between the monitor
          and the probe. Also, if the monitor doesn't have it already, implement a variable that counts all valid items.

        - Include the ThroughputProbe in your cocotb test.

        - When initializing the class, pass the custom probe interface connected to the monitor of the desired bus.
          Additionally, pass any other voluntary parameters if you wish to use them. A very useful is throughput_units,
          where you can choose from items, bits, or bytes per second.

        - Add time intervals where the probe shall log the immediate throughput and efficiency. For this, use the
          add_log_interval function from the parent class cocotbext.probe. For logging during the whole test, set
          the interval (0, None), but don't forget to set a period.

        - To set the logging period, use set_log_period from the parent class. If the period isn't set, the logging
          will take place when the interval ends. Note: if you have an interval going into infinity (the stop time
          is None), it will never log.

        - It's also possible to start and end the intervals manually with the start_log and stop_log functions from
          the parent class.

        - To get the average throughput and efficiency, call the log_average_throughput class.
          This is usually done at the end of the test.
    """
    def __init__(self, interface: ThroughputProbeInterface = None, period: int = 0, throughput_units: str = "items", time_units: str = "us", log_intervals: list = [], callback=None):
        super().__init__(interface, period, time_units, log_intervals, callback)
        self._total_item_cnt = 0
        self._clear_log_values()
        self._throughput_units = throughput_units.lower()

        if self._throughput_units not in ["items", "bits", "bytes"]:
            raise ValueError(f"Unknown throughput units '{self._throughput_units}'. Possible units are: 'items', 'bits', 'bytes'.")

    def log_average_throughput(self, throughput_units: str = None) -> None:
        """Prints out average throughput and efficiency."""
        throughput, throughput_units = self._convert_throughput_units(self._get_average_throughput(), throughput_units)
        self.log.info(f"Average throughput: {round(throughput, 4):,} {throughput_units}/s, Average efficiency: {round(self._get_average_efficiency()*100, 4)}%")

    def log_max_throughput(self, throughput_units: str = None) -> None:
        """
        Prints out result of _get_max_throughput function

        Args:
            throughput_units: how big unit should throughput use, optimal units: 'k'(ilo), 'M'(ega), 'G'(iga), 'T'(era).
                              If None, units are chosen automatically based on the calculated throughput.
        """
        throughput, throughput_units = self._convert_throughput_units(self._get_max_throughput(), throughput_units)
        self.log.info(f"Aproximate maximum possible throughput: {round(throughput, 4):,} {throughput_units}/s")

    def _clear_log_values(self) -> None:
        """Clears critical values used for logging."""
        self._log_vals_cleared = True
        self._start_of_period = 0
        self._total_item_cnt_at_start_of_period = 0
        self._vld_item_cnt_at_start_of_period = 0

    def _convert_throughput_units(self, value: int, throughput_mult_units: str) -> (float, str):
        """
        Converts base throughput units (Items/s) into ideal or specified multiples. Keeps them in items or converts
        them to bits or bytes depending on the specification of throughput_units value during init.

        Args:
            value: throughput in base units.
            throughput_mult_units: units to which it's to be converted. If None, the most appropriate is chosen.

        Returns:
            float: throughput in converted units.
            str: units to which it has been converted.
        """
        convertions = {"items": [1, "Items"], "bits": [self._interface.item_width, "b"], "bytes": [self._interface.item_width / 8, "B"]}

        value = value * convertions[self._throughput_units][0]
        throughput, throughput_mult_units = convert_units(value, "", throughput_mult_units)
        throughput_units = throughput_mult_units + convertions[self._throughput_units][1]

        return throughput, throughput_units

    def _log_immediate_throughput(self, period: int, time_units: str = "us", throughput_units: str = None) -> None:
        """
        Logs throughput of the bus in a section of specified length (period).

        Args:
            period: length of the sections during which the throughput is measured.
            time_units: unit of the period.
            throughput_units: how big unit should throughput use, optimal units: 'k'(ilo), 'M'(ega), 'G'(iga), 'T'(era).
                              If None, units are chosen automatically based on the calculated throughput.
        """
        gst_time_units = self._format_units_for_get_sim_time(time_units)

        if len(self._log_intervals) == 0:
            self._clear_log_values()
            return

        if self._simtime_is_in_log_interval():
            if self._log_vals_cleared:
                self._log_vals_cleared = False

                start_time, stop_time, units, _ = self._log_intervals[0]
                self._start_of_period = convert_units(start_time, units.strip("s"), time_units.strip("s"))[0]
                self._total_item_cnt_at_start_of_period = self._total_item_cnt
                self._vld_item_cnt_at_start_of_period = self._interface.item_cnt

            else:
                if period == 0:
                    return

                time_diff = round(get_sim_time(units=gst_time_units) - self._start_of_period, 4)

                if time_diff >= period:
                    throughput_base_units = (self._interface.item_cnt-self._vld_item_cnt_at_start_of_period) / convert_units(period, time_units.strip("s"), "")[0]
                    throughput, throughput_units = self._convert_throughput_units(throughput_base_units, throughput_units)

                    efficiency = self._get_immediate_efficiency()*100

                    self.log.info(f"Immediate throughput at {get_sim_time(units=gst_time_units)} {time_units}: {round(throughput, 4):,} {throughput_units}/s, Immediate efficiency: {round(efficiency, 4)}%")

                    self._start_of_period = get_sim_time(units=gst_time_units)
                    self._total_item_cnt_at_start_of_period = self._total_item_cnt
                    self._vld_item_cnt_at_start_of_period = self._interface.item_cnt

        else:
            self._clear_log_values()

    def _get_immediate_efficiency(self) -> float:
        """
        Calculates efficiency of the bus transfers during a specified period. Called by function _log_immediate_throughput.

        Returns:
            immediate efficiency as a decimal number (0 <= n <= 1).
        """
        delta_vld_items = self._interface.item_cnt-self._vld_item_cnt_at_start_of_period
        delta_total_items = self._total_item_cnt-self._total_item_cnt_at_start_of_period

        if delta_total_items == 0:
            raise ZeroDivisionError("Tried to get immediate efficiency with no items comming through.")

        return delta_vld_items/delta_total_items

    def _get_average_throughput(self) -> float:
        """
        Current average throughput calculated from all items and simulation time.

        Returns:
            average throughput in base units (either Items/s, b/s or B/s depending on which units are set).
        """
        return self._interface.item_cnt/get_sim_time(units="sec")

    def _get_max_throughput(self) -> float:
        """
        Calculates approximate maximum throughput based on the total possible items and current simulation time.

        Returns:
            Approximate maximum throughput in base units (either Items/s, b/s, or B/s, depending on which units are set).
            Can be a little inaccurate, especially when called at the end of the simulation, because of the period when
            all the transactions have been already received but the simulation hasn't ended yet. The best accuracy can be
            achieved in the middle of the simulation.
        """
        return self._total_item_cnt/get_sim_time(units="sec")

    def _get_average_efficiency(self) -> float:
        """
        Calculated average efficiency from all items at the specified point.

        Returns:
            average efficiency as a decimal number lower than or equal to one.
        """
        return self._interface.item_cnt/self._total_item_cnt

    async def _start_probe(self) -> None:
        """
        The main function incrementing the number of possible items and running the function for immediate logging
        each clock cycle.
        """
        while True:
            await self._clk_re

            if self._interface.in_reset:
                continue

            self._total_item_cnt += self._interface.items

            self._log_immediate_throughput(round(self._get_log_period(), 4), self._time_units)
