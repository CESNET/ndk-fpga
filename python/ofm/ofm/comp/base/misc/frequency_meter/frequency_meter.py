from typing import Tuple, List, Optional
import argparse
from tabulate import tabulate

import nfb
from ofm.utils import convert_units


class FrequencyMeter(nfb.BaseComp):
    DT_COMPATIBLE = "cesnet,ofm,frequency_counter"

    ## Addresses of the component's MI registers
    _REG_COMMAND   = 0x00 # Write commands (control register)
    _REG_STATUS    = 0x04 # Read status
    _REG_INTERVAL  = 0x08 # Read/Write length of the measurement interval
    _REG_REF_FREQ  = 0x0C # Read the Reference frequency
    _REG_MSR_FREQS = 0x10 # Read the number of measured frequencies
    _REG_REF_DATA  = 0x14 # Read the Reference counter's data
    _REG_MSR_DATA  = 0x18 # Read the Measured counter's data
    _REG_RD_PTR    = 0x1C # Read the Read pointer (id which Measured counter's data are read)

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        try:
            self.__default_interval     = self._comp.read32(self._REG_INTERVAL)
            self.__reference_frequency  = self._comp.read32(self._REG_REF_FREQ)
            self.__measured_frequencies = self._comp.read32(self._REG_MSR_FREQS)
        except BaseException:
            raise BaseException("Reading data from the FPGA fw failed :_(")

        # A dictionary with errors in the Status register (=properties) as keys and
        # their description messages as values.
        self.__errors = {
            "ref_cntr_overflowed" : "the Reference Frequency counter overflowed"          ,
            "meas_cntr_overflowed": "at least one Measured Frequency counter overflowed"  ,
            "ref_runtime_reset"   : "the Reference clock was reset during the measurement",
            "meas_runtime_reset"  : "at least one of the Measured clocks was reset during \
                                     measurement"                                         ,
        }

    @property
    def default_interval(self) -> int:
        return self.__default_interval

    @property
    def reference_frequency(self) -> int:
        return self.__reference_frequency

    @property
    def measured_frequencies(self) -> int:
        return self.__measured_frequencies

    # ################################
    # Methods for the Command register
    # ################################
    def start(self) -> None:
        """Start the measurement.

        Enables the Frequency counters for the duration of Interval length clock cycles.

        Note: does not check the Ready bit in the Status register prior the command.
        """
        self._comp.write32(self._REG_COMMAND, 1)

    def stop(self) -> None:
        """Stop the "Frequency counters".

        After stopping, the measurement can be continued by issuing the `start` or restarted
        just by issuing the `reset`.
        """
        self._comp.write32(self._REG_COMMAND, 0)

    def reset(self) -> None:
        """Reset the measurement logic.

        Issuing a reset during a measurement will result in the measurement starting anew.
        Note: results from previous measurements are reset too.
        """
        self._comp.write32(self._REG_COMMAND, 2)

    def fetch(self) -> None:
        """Load data from the Counters to the MI registers if they are ready."""
        self._comp.write32(self._REG_COMMAND, 4)

    # ###########################################
    # Methods (proprties) for the Status register
    # ###########################################
    @property
    def status(self) -> int:
        """Get the value of the Status register (all status bits together)."""
        return self._comp.read32(self._REG_STATUS)

    @property
    def ready(self) -> bool:
        """Return True if the component is ready to start another measurement."""
        return self._comp.get_bit(self._REG_STATUS, 0)

    @property
    def enabled(self) -> bool:
        """Return True if the measurement is under way."""
        return self._comp.get_bit(self._REG_STATUS, 1)

    @property
    def done(self) -> bool:
        """Return True when the measurement interval ended."""
        return self._comp.get_bit(self._REG_STATUS, 2)

    @property
    def fetchable(self) -> bool:
        """Return True when the measurement data are ready to be fetched to the MI registers."""
        return self._comp.get_bit(self._REG_STATUS, 3)

    @property
    def fetched(self) -> bool:
        """Return True when the measurement data were fetched successfully."""
        return self._comp.get_bit(self._REG_STATUS, 4)

    @property
    def errored(self) -> bool:
        """Return True if an error occurred during the measurement.

        The exact error is indicated by one of the following four Status bits (5-8).
        """
        return self._comp.get_bit(self._REG_STATUS, 5)

    @property
    def ref_cntr_overflowed(self) -> bool:
        """Return True if the Reference counter overflowed during the measurement."""
        return self._comp.get_bit(self._REG_STATUS, 6)

    @property
    def meas_cntr_overflowed(self) -> bool:
        """Return True if at least one Measured counter overflowed during the measurement."""
        return self._comp.get_bit(self._REG_STATUS, 7)

    @property
    def ref_runtime_reset(self) -> bool:
        """Return True if Reset on the Reference clock came during the measurement."""
        return self._comp.get_bit(self._REG_STATUS, 8)

    @property
    def meas_runtime_reset(self) -> bool:
        """Return True if Reset on one of the Measured clocks came during the measurement."""
        return self._comp.get_bit(self._REG_STATUS, 9)

    # ########################################
    # Methods (properties) for other registers
    # ########################################
    @property
    def interval(self) -> int:
        """Get the length of the measuring interval as a number of MI clock cycles."""
        return self._comp.read32(self._REG_INTERVAL)

    @interval.setter
    def interval(self, interval: int) -> None:
        """Set the length of the measuring interval as a number of MI clock cycles."""
        if interval > 2**32 - 1:
            raise OverflowError(f"Max value for the interval is 2**32-1 (got {interval})!")
        self._comp.write32(self._REG_INTERVAL, interval)

    @property
    def reference_data(self) -> int:
        """Get the data from the Reference frequency counter."""
        return self._comp.read32(self._REG_REF_DATA)

    @property
    def measured_data(self) -> List[int]:
        """Get the data from the Measured frequency counter(s)."""
        lst = []
        for _ in range(self.measured_frequencies):
            lst.append(self._comp.read32(self._REG_MSR_DATA))
        return lst

    @property
    def read_pointer(self) -> int:
        """Get the ID of the Measured frequency counter, whose data will be read next.

        Returns:
        A value in the range from 0 to measured_frequencies-1 indicating the index of the
        Measured frequency counter that will be read next.
        """
        return self._comp.read32(self._REG_RD_PTR)

    # ###################
    # Abstraction methods
    # ###################
    def get_measured_data(self) -> Tuple[int, List[int]]:
        """Fetch Reference and Measured data from the counters.

        It reads data from the MI registers to which the data from the counters are
        first fetched (pre-loaded). It waits in a loop until the "fetchable" flag (Status bit 4)
        is asserted. It can get stuck in the waiting loop in case of an error.

        Returns:
        A Tuple with the Reference data and a list of N Measured data.
        """
        # Fetch measurement results to the MI registers
        while not self.fetchable:
            continue
        self.fetch()

        # Read the fetched data
        while not self.fetched:
            continue
        return (self.reference_data, self.measured_data)

    def calculate(self, r_data: int, m_data: int, r_freq: Optional[int] = None) -> float:
        """Calculate the frequency of a single measured signal in Hz."""
        if r_freq is None:
            r_freq = self.reference_frequency

        return r_freq * m_data / r_data

    def calculate_n(self, r_data: int, m_data: List[int], r_freq: Optional[int] = None) -> List[float]:
        """Calculate frequencies of N measured signals with the same reference signal.

        Args:
        r_data: Value from the Reference frequency counter.
        m_data: Values from the Measured frequency counters.
        r_freq: Option to set the reference frequency; uses the default from FW when unset.

        Returns:
        A list of measured frequencies in Hz. The indexes correspond with the frequency_meter's
        ports (and to which signals they are connected in the FW).
        """
        if r_freq is None:
            r_freq = self.reference_frequency

        results = []
        for md in m_data:
            # TO Test: readpointer
            self.read_pointer
            results.append(self.calculate(r_data, md, r_freq))
        return results

    def measure(self, indexes: Optional[List[int]] = None, interval: Optional[int] = None) -> List[Tuple[float, str]]:
        """Abstracts the whole task of measuring the frequency.

        Args:
        indexes: Get measured frequencies on the given indexes that correspond with how is the FW
                 component connected (which signal is connected to which port).
        interval: Option to set the length of the measuring interval here instead of using the
                  'interval' property.

        Returns:
        A list of measured frequencies and its units as a Tuple[frequency, unit].

        Raises:
        RuntimeError: When a measurement error is detected (=measured frequencies are invalid).
        """
        if indexes is not None:
            raise NotImplementedError("Please, do not set this argument. \
                It is not possible to measure only some indexes at this time.")

        if interval is not None:
            self.interval = interval

        self.reset()

        # Launch the measurement
        while not self.ready:
            continue
        self.start()

        # Calculate the frequencies
        r_freq, m_freqs = self.get_measured_data()
        if self.errored:
            msg = ["Some errors occurred during the measurement:"]
            msg.extend(self.get_errors())
            smsg = "\n\t- ".join(msg)
            raise RuntimeError(smsg)
        freqs = self.calculate_n(r_freq, m_freqs)

        # Covert and format the measured frequencies
        freqs_units = []
        for f in freqs:
            val, unit = convert_units(f)
            freqs_units.append((val, unit + "Hz"))
        return freqs_units

    def get_errors(self) -> List[str]:
        """Return a list with descriptions of the errors that occurred during the measurement.

        Goes through all the possible errors listed in the "self.__errors" dictionary.
        Appends the description of those that occurred during the last measurement.
        """
        ret = []
        for e in self.__errors.keys():
            # Each iteration issues an MI read32 and gets a single bit (optimization possible)
            if getattr(self, e):
                ret.append(self.__errors[e])
        return ret

    def print_errors(self, errors: Optional[List[str]] = None) -> None:
        """Prints the info about the errors that occurred during the measurement."""
        if errors is None:
            errors = self.get_errors()

        if errors:
            print("Measurement errors: ", *errors, sep="\n\t- ")
        else:
            print("No errors occurred during the measurement! Congratulations!")


# ########################
# The frequency-meter tool
# ########################
def tabulate_data(data: List[Tuple[float, str]]) -> str:
    """Format the measured data (list of tuples of the frequency and its units) to a table."""
    headers = ["#", "Frequency", "Units"]
    rows = []
    for f, u in data:
        rows.append([f, u])
    return tabulate(rows, headers=headers, showindex=True, floatfmt=".2f", tablefmt="grid")


def main():
    help_dict = {
        "device"   : "set the target device",
        "interval" : "set the duration of the measurement in the number of clock cycles",
        "measure"  : "run the measurement and print results",
        "settings" : "print current settings of the FrequencyMeter (interval, ref frequency, ...)",
        "errors"   : "print information about occurred errors",
    }

    arg_parser = argparse.ArgumentParser(
        prog="frequency-meter",
        description="Communicates with the FREQUENCY_METER firmware component in the card to \
                    measure clock frequencies."
    )
    arg_parser.add_argument("-d", "--device", default=nfb.default_dev_path, help=help_dict["device"])
    arg_parser.add_argument("-i", "--interval", type=int, help=help_dict["interval"])
    arg_parser.add_argument("-m", "--measure", action="store_true", help=help_dict["measure"])
    arg_parser.add_argument("-s", "--settings", action="store_true", help=help_dict["settings"])
    arg_parser.add_argument("-e", "--errors", action="store_true", help=help_dict["errors"])
    args = arg_parser.parse_args()

    try:
        fm = FrequencyMeter(dev=nfb.open(args.device))
    except IndexError:
        raise IndexError("Could not open the FrequencyMeter component (FW).")

    if args.interval:
        fm.interval = args.interval

    if args.measure:
        data = fm.measure()
        print(tabulate_data(data))

    if args.settings:
        print(f"Length of the measurement interval: {fm.interval:,} clock cycles.")
        val, unit = convert_units(fm.reference_frequency)
        print(f"Reference frequency: {val} {unit}Hz.")
        print(f"Number of measured frequencies: {fm.measured_frequencies}.")

    if args.errors:
        fm.print_errors(fm.get_errors())


if __name__ == "__main__":
    main()
