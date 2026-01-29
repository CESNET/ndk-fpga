import cocotb
import cocotb_bus.drivers as cbd
import cocotb_bus.monitors as cbm
from cocotb_bus.monitors import MonitorStatistics

from collections import deque
from cocotb.triggers import Event
from cocotb.log import SimLog


class Driver:
    def __init__(self):
        """Constructor for a driver instance."""
        self._pending = Event(name="Driver._pending")
        self._sendQ = deque()
        self.busy_event = Event("Driver._busy")
        self.busy = False

        # Sub-classes may already set up logging
        if not hasattr(self, "log"):
            self.log = SimLog("cocotb.driver.%s" % (type(self).__qualname__))

        # Create an independent coroutine which can send stuff
        self._thread = cocotb.start_soon(self._send_thread())


class Monitor:
    def __init__(self, callback=None, event=None):
        self._event = event
        self._wait_event = Event()
        self._recvQ = deque()
        self._callbacks = []
        self.stats = MonitorStatistics()

        # Sub-classes may already set up logging
        if not hasattr(self, "log"):
            self.log = SimLog("cocotb.monitor.%s" % (type(self).__qualname__))

        if callback is not None:
            self.add_callback(callback)

        # Create an independent coroutine which can receive stuff
        self._thread = cocotb.start_soon(self._monitor_recv())


def do_fix():
    cbd.Driver.__init__ = Driver.__init__
    cbm.Monitor.__init__ = Monitor.__init__
