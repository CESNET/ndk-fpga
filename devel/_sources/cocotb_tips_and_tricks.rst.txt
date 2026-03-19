====================
Cocotb tips & tricks
====================

This section consists of simple problems you may encounter when creating testbenches
using ``cocotb/cocotbext-ndk`` frameworks and the solutions to those problems.

Using probes
============

``cocotbext-ndk`` framework includes a base class for creating probes for various purposes.
It can be found at ``ndk-fpga/python/cocotbext/cocotbext/ofm/base/probe.py``. The
probes typically read attributes of their connected agents, usually a monitor or a driver,
perform calculations with them, and display the results to the terminal either at a specific
time, periodically, or on request.

The base ``Probe`` class offers a couple of methods to make this possible.

To log a specific time interval, use the ``add_log_interval`` method. If you want the time interval
to go to infinity, set the ``stop_time`` argument to ``None``; however, don’t forget to also set a period,
otherwise the probe will never log.

Periodic logging can be achieved by setting a period using the ``set_log_period`` method.

For cases where full control over when the probe starts and stops logging is needed, the ``start_log``
and ``stop_log`` methods are implemented.

When it comes to specific implementations of probes, at the time of writing, there is only one,
and that is ``ThroughputProbe`` for measuring throughput and efficiency.
Check out ``ndk-fpga/python/cocotbext/cocotbext/ofm/utils/throughput_probe.py`` for the implementation.

Class ``ThroughputProbe`` further adds the ``log_average_throughput`` and ``log_max_throughput`` methods
to log the average throughput and efficiency and the maximal possible average throughput,
respectively. It is recommended to call these methods at the end of the test when all the transactions
have been processed.

To perform its task, a probe typically needs to read attributes from the probed agent synchronously.
However, the names of the attributes of the agent may differ from the names of the attributes of the probe,
or they may not be present at all; in that case, they need to be either calculated or set to a fixed value.

To resolve this, it is recommended to use interfaces derived from the ``ProbeInterface`` class. This class
offers two approaches for passing a value to the probe – a translation dictionary ``interface_dict`` and
properties.

The translation dictionary ``interface_dict`` should contain all needed attributes as its keys.
The values linked to the keys should be either the names of the equivalent attributes of the agent,
or ``None`` to indicate that the value is returned by a property of the interface.

If the value cannot be simply read from the agent object because some logic needs to be performed
(e.g., the value must be calculated from multiple attributes, or the behavior depends on the type of the
agent), a property with the same name as the key in ``interface_dict`` can be created, which overrides the
dictionary entry.

.. note:: The interface always looks for a property first. Only after it is not found does it try to get the value
   from the connected agent using ``interface_dict``.

For a specific implementation of a probe interface, check out the different interfaces for
``ThroughputProbe`` in ``ndk-fpga/python/cocotbext/cocotbext/ofm/utils/throughput_probe.py``.

The setup of a probe can, for example, look like this:

.. code-block:: python

    self.out_throughput_probe = ThroughputProbe(
        ThroughputProbeMfbInterface(self.stream_out),
        throughput_units="bits",
        name="ThroughputProbe - OUT"
    )
    self.out_throughput_probe.add_log_interval(0, None)
    self.out_throughput_probe.set_log_period(10)

Which then produces output like this:

.. code-block::

    #  10000.00ns INFO     cocotb.ThroughputProbe - OUT       Immediate throughput at 10.0 us: 134.5104 Gb/s, Immediate efficiency: 32.8395%
    #  20000.00ns INFO     cocotb.ThroughputProbe - OUT       Immediate throughput at 20.0 us: 134.8456 Gb/s, Immediate efficiency: 32.9213%
    #  30000.00ns INFO     cocotb.ThroughputProbe - OUT       Immediate throughput at 30.0 us: 134.9 Gb/s, Immediate efficiency: 32.9346%
