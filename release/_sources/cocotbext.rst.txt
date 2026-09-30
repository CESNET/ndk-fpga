.. _cocotbext-ndk:

=============
cocotbext-ndk
=============

``cocotbext-ndk`` is a Python package extending the ``cocotb`` framework. It is not intended as its replacement.
The NDK uses it to verify VHDL components, potentially in combination with associated software (Python module).

The base directory of ``cocotbext-ndk`` is located in ``ndk-fpga/python/cocotbext``.


Motivation
==========

``cocotbext-ndk`` was created to improve and extend ``cocotb`` in areas where we found it lacking while implementing verifications of modules
included in ndk-fpga. It's meant to improve and simplify the implementation of simulations and verifications for high-speed networking devices
and is much better adapted for this purpose compared to base ``cocotb``. Some modules can also be found useful in the verification of other types
of devices.

``cocotbext-ndk`` notably adds:

- drivers and monitors for various buses
- requesters and completers for PCIe
- rate limiters
- probes
- generators
- transaction objects
- interfaces for ``libnfb``
- a collection of useful utilities

Modules
=======

The following section describes a few notable modules in ``cocotbext-ndk``.

cocotbext.ofm.base
------------------

This module includes base classes that are meant to be extended for specific purposes. You may find these very useful while creating
a verification of hardware with interfaces that are not supported by ``cocotbext-ndk``.

.. rubric:: drivers.BusDriver

Extended BusDriver found in ``cocotb_bus.drivers.BusDriver``.

It adds common functionality like:

* ``RisingEdge`` clock event (``self._clk_re``)
* Configuration (``self._cfg``) can be used, for example, to configure a specific idle generator
* Idle generator (default is ``IdleGenerator``, which doesn't generate any idles)

.. note:: Can be used as a drop-in replacement for ``cocotb_bus.BusDriver`` with more creature comforts.

.. rubric:: generators.IdleGenerator

Idle generator ensures the interlacing of idle and data transactions in drivers.

Idle generators can adopt various behaviors such as "no idles" (full throughput on bus),
"random idles", "rate limiter", etc.

This base ``IdleGenerator`` generates no idles.

A driver uses the idle generator by calling a pair of ``.get`` and ``.put`` methods.
The ``get`` method returns a number of idle items which should be inserted on the bus.
The ``put`` method awaits the number of idle items that were inserted onto the bus (may have been more or less than what the `get()` method returned).

Some idle generators need to know more about the bus parameters and should be parametrized
with a proper configure call.

.. rubric:: generators.EthernetRateLimiter

Limits throughput to achieve a specified maximum rate on Ethernet by generating ``IdleTransaction``.
Considers SFD, CRC, and IPG in its calculation of the current throughput.
Typically applicable for a byte-oriented data bus like the MFB, AXI-stream, etc.

Ensure the driver puts a transaction with the "end" argument.

.. rubric:: generators.ItemRateLimiter

Limits throughput to achieve a specified rate by generating ``IdleTransaction``.
Typically applicable for a value-oriented data bus like the MVB.

.. note:: ``IdleGenerator``, ``EthernetRateLimiter`` and ``ItemRateLimiter`` are useful for generating empty, non-valid transactions during
    verifications to make the traffic more realistic.

.. rubric:: probe.Probe

Generic probe class used for probing specific parameters of a simulated component.

This class by itself does nothing. It is a generic class made to be derived from for specific use cases.

.. note:: Useful for logging values of interest. Check out ``cocotbext.ofm.utils.throughput_probe.ThroughputProbe`` for specific implementation.

.. rubric:: probe.ProbeInterface

Generic class for translating attributes of monitors to probe attributes.

.. note:: Creates a link between ``Probe`` and a connected object. See ``cocotbext.ofm.utils.throughput_probe.ThroughputProbeInterface`` for specific implementation.

.. rubric:: proxymonitor.ProxyMonitor

Abstract proxy monitor, which is used for redirecting traffic from ``BusMonitor`` from ``cocotb_bus.monitors`` and running it through a filter. It automatically
connects to the ``_recv`` function of the passed ``BusMonitor``.

.. note:: Useful for filtering out unwanted transactions or modifying transactions before passing them down to a test without
    modifying the monitor itself, which allows you to have a generic monitor and use proxy monitors for special needs.
    Check out ``cocotbext.ofm.mi.proxymonitor.MIProxyMonitor`` for specific implementation.

.. rubric:: transaction.BaseTransaction

Base class for transactions. All other transaction types inherit from this class.

.. rubric:: transaction.IdleTransaction

Transaction represents general bus idling.

There is no exact size of ``IdleTransaction``; it should represent the
smallest unit of data that the bus can transfer. For example,
one byte on the MFB bus, one item on the MVB bus, one word (clock cycle) on
common buses.

.. rubric:: transaction.Transaction

Transactions with real data to be written onto the bus.

It is possible to also find this class under the alias **DataTransaction**.

.. note:: The main advantage is that you see which signals the transaction includes and expects to be set in the declaration of the class
    and their type. Check out ``cocotbext.ofm.mi.transaction`` for specific implementations.

cocotbext.ofm.utils
-------------------

This module includes many tools that you may find useful while implementing verifications.

.. rubric:: device.get_dtb

Creates a Device Tree represented as a binary blob.

.. rubric:: servicer.Servicer

Allows to perform read and write operations on a component accessed via a Device Tree.

.. note:: A Device Tree in conjunction with ``Servicer`` allows you to simulate the behavior of (if applicable) an associated Python module that controls the component.

    Check out ``ndk-fpga/comp/mvb_tools/storage/mvb_hash_table_simple/cocotb/cocotb_test.py`` for example use in a test.

    Check out ``ndk-fpga/python/ofm/ofm/comp/mvb_tools/storage/mvb_hash_table_simple/mvb_hash_table_simple.py`` for an example of an associated Python module.

.. rubric:: header.SerializableHeader

Class for storing a packet header. It is possible to represent the header either as a dictionary (to work with individual fields) or an integer (for transmission/reception).

.. note:: The class is handy for working with packet headers - easy packing into an integer and unpacking into a dictionary.
    Check out ``cocotbext.ofm.pcie.AvstCompleter`` to see specific use cases.

.. rubric:: header.concat

Converts a list of values into an integer.

.. rubric:: header.deconcat

Converts an integer into a list of values.

.. rubric:: header.byte_serialize

Breaks down a large integer into a list of 8-bit integer values.

.. rubric:: header.byte_deserialize

Combines a list of integers (using their lower 8 bits) into a single large integer.

.. rubric:: math.ceildiv

Calculates into how many transmissions a transaction must be divided.

.. note:: In other words, how many words do I need to send a transaction of this length? Very commonly used in drivers and tests.

.. rubric:: math.numberOfSetBits

Counts the number of bits that are set to a logical 1 in an integer (after conversion to binary).

.. rubric:: math.bitmask

Returns a bitmask as an integer of a specified length.

.. note:: Usually used to generate value of signals indicating validity of the data. If used for this purpose, all of the data would
    be indicated as valid.

.. rubric:: ram.RAM

Simulated RAM component implemented in Python.

.. rubric:: signals.await_signal_sync

Synchronously waits until the value of the signal is equal to the required value.

.. note:: In drivers, monitors, and tests, waiting for the activation of a certain signal, such as a valid signal or a ready signal, is a very
    common occurrence. If the awaited signal is already set, the function returns with no delay; otherwise, it waits
    until the next rising edge of the clock signal and checks the value again.

.. rubric:: signals.get_signal_value_in_bytes

Gets the value of OUT signals in bytes.

.. note:: Simply retrieves the value of a signal, configures its endianness, and returns it as bytes. Nothing groundbreaking, it just hides
    three lines into one. Useful if you require bytes in little-endian rather than the default big-endian.

.. rubric:: signals.filter_bytes_by_bitmask

Filters the input bytes by a given bitmask.

.. note:: On some interfaces, not all transferred data bytes are valid, or in other terminology, shouldn't be kept. Which ones are and
    aren't valid is usually indicated by another signal that is a bitmask of the data signal. This function takes data and the bitmask as
    arguments, removes bytes that are not valid completely, and merges the ones that are valid into one ``bytes`` object, which it then returns.

.. rubric:: signals.align_request

Aligns the address and byte enable of a continuous request based on the bus width.

.. note:: Some interfaces do not accept requests where the address isn't aligned based on the width of the bus. This function takes the width
    of the bus, the address, and the length of the data that is sent with the request, optionally byte_enable, and determines how many bytes should
    be added to the front and back of the transaction, the aligned address, and the new byte enable. The function is a little complicated but
    it certainly can save you time when you need to align a request.

.. rubric:: signals.align_write_request

Aligns data, address, and byte enable of a continuous write request based on the bus width.

.. note:: Same function as ``signals.align_request``, but instead of the length of the data, it accepts the data itself, which it also
    returns aligned. Useful for aligning write requests as the name suggests.

.. rubric:: signals.align_read_request

Aligns the address and byte enable of a continuous read request based on the bus width.

.. note:: Same function as ``signals.align_request``, but in addition, it also returns how many bytes should actually be read
    and their byte enable to compensate for the non-aligned address.

.. note:: For an example use of the align functions, please refer to the ``cocotbext.ofm.mi.driver`` module.

.. rubric:: signals.wait_number_of_cycles

Waits for the specified number of clock cycles.

.. rubric:: signals.set_signal_delayed

Sets a signal after waiting a certain amount of clock cycles.

.. note:: The two functions ``signals.wait_number_of_cycles`` and ``signals.set_signal_delayed`` are usually used in cases where
    a signal should be set after a random number of cycles in a range. The number of cycles in those cases is generated by
    the ``random.randint`` function.

.. rubric:: throughput_probe.ThroughputProbe

Probe for measuring and logging throughput and efficiency.

.. note:: Great for measuring the throughput and efficiency of a component under different loads, which can be simulated by e.g., using rate limiters.

.. rubric:: throughput_probe.ThroughputProbeInterface

Base class for interfacing between a throughput probe and a ``BusMonitor`` object. By itself, it does nothing;
it should be used as a template (to see which attributes a throughput probe requires in the ``interface_dict``).

.. note:: Allows you to easily create an interface to be able to use ``ThroughputProbe`` with bus not supported by ``cocotbext-ndk``.

.. rubric:: throughput_probe.ThroughputProbeMvbInterface

Throughput probe interface for ``MVBMonitor``.

.. rubric:: throughput_probe.ThroughputProbeMfbInterface

Throughput probe interface for ``MFBMonitor``.


.. rubric:: ``EXPERIMENTAL`` binary.BinaryConvertions

Collection of operations with binary numbers represented by a list of ones and zeros.

They are intended for ``Binary``, but they can be useful if you can't or don't want to use
``Binary`` for whatever reason.

.. rubric:: ``EXPERIMENTAL`` binary.Binary

Class for easier storing of and working with binary numbers.

.. rubric:: ``EXPERIMENTAL`` binary.BinaryVector

Vector of binary numbers.
In reality, it's just ``Binary`` divided into smaller sections of fixed length that can be indexed (aka 'items' of an array).

.. rubric:: ``EXPERIMENTAL`` binary.BinarySignals

Interface for converting values read from ``cocotb.bus`` to ``Binary`` and ``BinaryVector``.

.. note:: ``Binary``, ``BinaryVector`` and ``BinarySignals`` were created to make working with segmented buses simpler
    and more readable. They are **highly experimental** and should be used with caution.

    You can see them in action in drivers and monitors in the ``cocotbext.ofm.mac_segmented`` module.


cocotbext.ofm.ver
-----------------

Includes tools made to simplify the creation of verifications.

.. rubric:: generators.random_byte

Random byte generator.

.. rubric:: generators.random_bytes

Generates N random bytes from the passed generator.

.. rubric:: generators.random_packets

Generates N random packets with random length of bytes in a min/max range.

.. rubric:: generators.random_integers

Generates N random integers between the min/max range.

.. rubric:: generators.random_transactions

Generates N random transactions based on the transaction type and the driver that is going to be used to send
the transaction. The driver object is used for getting the bit width of the signals that are set by the
transaction. The length of the transaction is random and between the specified minimum and maximum word count.
The value of every word is random by default. This can be changed by the ``patterns`` parameter, which accepts
a dictionary that has items of the following format: ``n: (f, a)``, where ``n`` is the name of the signal, ``f`` is a
function that is used to set the value of each word and ``a`` is a ``tuple`` of arguments that is given to the
function as args.

.. note:: Generators come in handy for easy generation of a large number of variable-length packets or transactions, which then
    can be passed to a driver and modeled as an expected output of a monitor.

.. rubric:: multibit_driver.MultiBitDriver

Extension of ``BitDriver`` from ``cocotb_bus.drivers`` capable of driving multiple bits instead of just one with
configurable driving patterns.
Useful for testing unstable ready and valid signals.

.. rubric:: multibit_driver.Patterns

Includes methods used with the ``MultiBitDriver`` as the ``pattern`` argument.
To be compatible with the driver, the methods should accept at least
two parameters: the width of the signal that is set and the
driver's state, which is either 0 as `off` or 1 as `on`. Other
parameters can be passed via the ``pattern_args`` tuple, which is passed
as args. A string of ones and zeros representing a binary number shall
be returned.

.. note:: ``MultiBitDriver`` is useful in these cases:

    - you have a component with a multi-bit ready signal and you want it to randomly activate and deactivate (which you usually want to properly verify that the behavior of the component is correct)
    - you want a little more control over the driven signal than the standard ``BitDriver`` provides, thanks to the configurable pattern function.

cocotbext.ofm.avst_eth
----------------------

Drivers and monitors for Avalon Streaming for Ethernet (Ethernet E-TILE interface).

.. rubric:: avst_eth.drivers.AvstEthDriver

Accepts whole packets as bytes and writes them to the master side of the bus.

.. rubric:: avst_eth.drivers.AvstEthMonitor

Reads whole packets from the slave side of the bus and returns them as bytes.

cocotbext.ofm.avst_pcie
-----------------------

Drivers, monitors, and credit interface controllers for Avalon Streaming for PCIe P-TILE and R-TILE interfaces.

.. rubric:: drivers.AvstPcieDriverMaster

Accepts whole request or completion packets as a dictionary and writes them to the master side of the bus.
Completions are prioritized.

.. rubric:: drivers.AvstPcieDriverSlave

Sets the ready signal of the slave side of the bus to logical 1.

.. rubric:: monitors.AvstPcieMonitor

Reads whole packets from the slave side of the bus and returns them as a tuple consisting of two bytearrays - the header bytearray
and the data bytearray.

.. rubric:: creditor.AvstCreditorStatesTX

States of the finite state machine of ``AvstCreditorTX``.

.. rubric:: creditor.AvstCreditorStatesRX

States of the finite state machine of ``AvstCreditorRX``.

.. rubric:: creditor.AvstTransactionTypes

Transaction types of Avalon Streaming for PCIe with their number codes.

.. rubric:: creditor.PcieTransactionTypes

Types of PCIe transactions with their codes supported by ``AvstCreditRequester`` and ``AvstCreditReceiver``.

.. rubric:: creditor.AvstCreditorTX

Driver controlling the TX side of the R-TILE credit interface.

.. rubric:: creditor.AvstCreditorRX

Driver controlling the RX side of the R-TILE credit interface.

.. rubric:: creditor.AvstCreditRequester

Catches transactions sent by ``AvstRequester`` and ``AvstCompleter`` and checks if there
are enough credits of the specific type to forward them to the ``AvstPcieDriverMaster``.
If not, they are stopped until there are enough credits. It also updates the number
of credits consumed by a transaction after letting it through.

.. rubric:: creditor.AvstCreditReceiver

Returns credits to the ``AvstCreditorTX`` when a transaction comes through. Also checks if there are enough
credits to send the transaction. If not, an exception is raised.

.. note:: Use the credit interface components only for R-TILE.

    For implementation of conditional switching between P-TILE and R-TILE, check out ``ndk-fpga/python/cocotbext/cocotbext/ndk_core/nfbdevice.py``.

cocotbext.ofm.axi4stream
------------------------

Drivers, monitors, and transactions for AXI4-Stream.

.. rubric:: drivers.Axi4StreamMaster

Writes either a whole packet or a single word to the master side of the bus. It is recommended to write whole packets, which
can be achieved by passing the packet as an Axi4StreamTransaction object. If a dictionary is passed, it is sent as a single
word for backward compatibility.

.. rubric:: drivers.Axi4StreamSlave

Sets the ``TREADY`` signal of the slave side of the bus to logical 1.

.. rubric:: monitors.Axi4Stream

Reads either a single word or a whole packet from the slave side of the bus and returns it. By default, a single word as a dictionary
is returned for backwards compatibility; however, this is deprecated. It is recommended to set the argument ``trans_type`` to ``Axi4StreamTransaction``
during initialization so a whole packet is returned as an ``Axi4StreamTransaction`` object.

.. rubric:: transaction.Axi4StreamTransaction

Basic transaction for AXI4-Stream that includes ``TDATA``, ``TUSER``, and ``TKEEP``.

.. rubric:: transaction.Axi4StreamTransactionWithSelect

Variant of ``Axi4StreamTransaction`` that includes selector ``SEL`` for use with AXIS Splitter component.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/python/cocotbext/cocotbext/ndk_core/nfbdevice.py``.

cocotbext.ofm.lbus
------------------

Drivers and monitors for LBus.

.. rubric:: drivers.LBusDriver

Accepts a whole packet as bytes and writes it to the master side of the bus.

.. rubric:: monitors.LBusMonitor

Reads a whole packet from the slave side of the bus and returns it as a list of integer values of the read bytes.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/python/cocotbext/cocotbext/ndk_core/nfbdevice.py``.

cocotbext.ofm.lii
-----------------

Drivers and monitors for low-latency Ethernet.

.. rubric:: drivers.LIIDriver

Accepts a whole packet as bytes and writes it to the master side of the bus.

.. rubric:: monitors.LIIMonitor

Reads a whole packet from the bus and returns it as bytes.

.. rubric:: monitors.LIIProtocolError

Exception generated by ``LIIMonitor`` (e.g. when duplicate start or end of frame is detected).

cocotbext.ofm.mac_segmented
---------------------------

Drivers and monitors for Mac Segmented Client Interface (Ethernet F-TILE interface).

.. rubric:: drivers.MAC_Segmented_RX_Driver

Accepts a whole packet as bytes and writes it to the RX side of the bus.

.. note:: For example use, see ``comp/nic/mac_lite/rx_mac_lite/comp/adapters/mac_seg/cocotb/cocotb_test.py``.

.. rubric:: monitors.MAC_Segmented_TX_Monitor

Reads a whole packet from the TX side of the bus and returns it as bytes.

.. note:: For example use, see ``comp/nic/mac_lite/tx_mac_lite/comp/adapters/mac_seg/cocotb/cocotb_test.py``.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/python/cocotbext/cocotbext/ndk_core/nfbdevice.py``.


cocotbext.ofm.mfb
-----------------

Drivers and monitors for MFB (Multi Frame Bus).

.. rubric:: drivers.MFBDriver

Accepts a whole packet as bytes and writes it to the master side of the bus.

.. rubric:: monitors.MFBMonitor

Reads a whole packet from the slave side of the bus and returns it as bytes.

.. rubric:: monitors.MFBProtocolError

Exception generated by ``MFBMonitor``.

.. rubric:: utils.get_mfb_params

Gets bus parameters for ``MFBDriver`` from a dictionary with parameters ``param_dic``. If ``param_dic`` is ``None``,
parameters are calculated automatically based on the connected signals.

.. rubric:: utils.signal_unpack

Splits the value of a signal into items and returns them as a list.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/comp/mfb_tools/storage/fifox/cocotb/cocotb_test.py``.

cocotbext.ofm.mi
----------------

Drivers, monitors, proxymonitors, and transactions for MI (Memory Interface).

.. rubric:: drivers.MIRequestDriver

Request driver intended for the MI bus that allows sending data to and receiving from the bus.

.. rubric:: drivers.MIResponseDriver

Response driver intended for the MI bus that allows sending data - responses to read requests - to the read signals of the bus.

.. rubric:: drivers.MIRequestDriverAgent

``MIRequestDriver`` with a ``_send_thread`` function. Intended for use in flow tests.

.. rubric:: drivers.MIResponseDriverAgent

``MIResponseDriver`` with a ``_send_thread`` function. Intended for use in flow tests.

.. rubric:: monitors.MIMonitor

Monitor intended for monitoring both sides of the MI bus.

.. rubric:: proxymonitor.MIProxyMonitor

Proxy Monitor intended for the ``MIMonitor``. Based on configuration lets through only request transactions (sent by master) or
only response transactions (sent by slave).

For example, two MI monitors are connected to an MI Pipe; one is connected to the request (master)
side and the other to the response (slave) side. When a transaction appears on
the pipe, it is detected by both monitors, and both generate an MI transaction
and send it to the scoreboard. However, only one of the two transactions is
the wanted one. If the transaction on the bus was a request transaction, the
transaction from the request monitor should be accepted, and vice versa.
The purpose of this monitor is to filter out the unwanted transactions.

.. rubric:: transaction.MiTransactionType

Enum of types of MI transactions.

.. rubric:: transaction.MiBaseTransaction

Base class for MI transactions with configurable data items.

.. rubric:: transaction.MiRequestTransaction

Transaction for ``MIRequestDriver``.

.. rubric:: transaction.MiResponseTransaction

Transaction for ``MIResponseDriver``.

.. rubric:: transaction.MiTransaction

Full MI transaction for monitor and test.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/comp/mi_tools/pipe/cocotb/cocotb_test.py`` and ``/ndk-fpga/comp/mi_tools/test_space/cocotb/cocotb_test.py``.

cocotbext.ofm.mvb
-----------------

Drivers, monitors, and transactions for MVB (Multi Value Bus).

This bus (its interface) can be quite versatile from the point of different data signals.
Other than ports for data data (and metadata), components can implement ports such as length, address, discard, and many more with possible different aliases.

If the current driver, monitor, or MVB transactions do not implement the necessary signals, it is advisable to
create your own (sub)classes for your specific usecase in your local Cocotb test directory.

.. rubric:: drivers.MVBDriver

Driver intended for the MVB bus used for sending transactions to the bus.

.. rubric:: monitors.MVBMonitor

Master monitor intended for monitoring the MVB bus.

.. rubric:: transaction.MvbTransaction

Base class for MVB Transactions with configurable data items.

.. rubric:: transaction.MvbTrClassic

Transaction for the MVB bus consisting of data only.

.. rubric:: transaction.MvbTrClassicWithMeta

Transaction for the MVB bus consisting of data and metadata.

.. rubric:: transaction.MvbTrAddressWithMeta

Transaction for the MVB bus consisting of an address and metadata.

.. note:: For example use of drivers and monitors, see ``ndk-fpga/comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py``.

cocotbext.ofm.pcie
------------------

Requesters, completers, and their headers for Avalon Streaming for PCIe and AXI4-Stream.

.. rubric:: AvstRequester.AvstBase

Base class for ``AvstCompleter`` and ``AvstRequester``.

.. rubric:: AvstRequester.AvstRequester

Handles inbound PCIe request transactions and their completions for the PCIe Avalon Streaming bus.
Requests are accepted from a monitor, processed here by the ``AvstRequester``, and stored in the RAM.
If the request requires a response (e.g., it is a read request), it also generates one (see the ``handle_response`` method)
and sends it to the bus using a driver.

.. rubric:: AvstRequester.CompletionHeaderEmpty

Empty header of a PCIe completion packet used by ``AvstRequester``.

.. rubric:: AvstRequester.RequestHeader

Header of a PCIe request packet used by ``AvstRequester``.

.. rubric:: AvstRequester.CompletionHeader

Header of a PCIe completion packet used by ``AvstRequester``.

.. rubric:: AvstCompleter.AvstCompleter

Handles outbound request transactions and their completions for the PCIe Avalon Streaming bus. Request transactions are created by the ``read``
and ``write`` methods (and their variants), and sent via a driver to the bus. Completions (for read requests) are then accepted by a monitor
and processed here by the ``AvstCompleter`` (see the ``_handle_cc_transaction`` method).

.. rubric:: AvstCompleter.RequestHeaderEmpty

Empty header of a PCIe request packet used by ``AvstCompleter``.

.. rubric:: AvstCompleter.RequestHeader

Header of a PCIe request packet used by ``AvstCompleter``.

.. rubric:: AvstCompleter.CompletionHeader

Header of a PCIe completion packet used by ``AvstCompleter``.

.. rubric:: Axi4SRequester.Axi4SRequester

Handles inbound request transactions and their completions for the PCIe AXI4-Stream bus. Requests are accepted from a monitor,
processed here by ``Axi4SRequester`` and are stored in RAM. If the request requires a reponse (e.g., it is a read request), it
also generates one (see the ``handle_response`` method) and sends it to the bus using a driver.

.. rubric:: Axi4SRequester.RequestHeader

Header of a PCIe request packet used by ``Axi4SRequester``.

.. rubric:: Axi4SRequester.CompletionHeader

Header of a PCIe completion packet used by ``Axi4SRequester``.

.. rubric:: Axi4SRequester.RqUser

Additional information for PCIe request packet sent via the ``TUSER`` signal of AXI4-Stream.

.. rubric:: Axi4SRequester.RcUser

Additional information for PCIe completion packet sent via the ``TUSER`` signal of AXI4-Stream.

.. rubric:: Axi4SRequester.Frame

Stores data, metadata, and the number of dwords of a packet.

.. note:: For example use of requesters and completers, see ``ndk-fpga/python/cocotbext/cocotbext/ndk_core/nfbdevice.py``.

.. rubric:: Axi4SCompleter.Axi4SCompleter

Handles outbound request transactions and their completions for the PCIe AXI4-Stream bus. Request transactions are created by the ``read``
and ``write`` methods (and their variants), and sent via a driver to the bus. Completions (for read requests) are then accepted by a monitor
and processed here by the ``Axi4SCompleter`` (see the ``_handle_cc_transaction`` method).

.. rubric:: Axi4SCompleter.RequestHeaderEmpty

Empty header of a PCIe AXI4-Stream request packet used by ``Axi4SCompleter``.

.. rubric:: Axi4SCompleter.RequestHeader

Header of a PCIe request packet used by ``Axi4SCompleter``.

.. rubric:: Axi4SCompleter.RequestUser

Additional information for PCIe request packet sent via the ``TUSER`` signal of AXI4-Stream.

.. rubric:: Axi4SCompleter.RequestUser512

Additional information for PCIe request packet sent via the ``TUSER`` signal of AXI4-Stream with 512 bit ``res1``.

.. rubric:: Axi4SCompleter.CompletionHeader

Header of a PCIe completion packet used by ``Axi4SCompleter``.

cocotbext.nfb
-------------

.. rubric:: device.NfbDevice

Abstract class representing an NFB device from the ``libnfb`` library.

.. rubric:: queue.QueueManager

Helper class for creating queues representing ``libnfb`` queues.

.. rubric:: queue.QueueNdp

For alternative, simplified NDP queue management in firmware.

.. rubric:: queue.QueueNdpRx

Implementation of ``QueueNdp`` for RX transactions.

.. rubric:: queue.QueueNdpTx

Implementation of ``QueueNdp`` for TX transactions.

cocotbext.nfb.ext.gprc
----------------------

.. rubric:: dma.DmaRequest

Encapsulates DMA transactions via gRPC used by ``DmaServicer``.

.. rubric:: dma.DmaServicer

Processes ``DmaRequest`` requests originating from the simulated design and transmitted via gRPC.
It represents a `reversed` gRPC usage: the DMA servicer runs on the client side (the program generating MI bus requests)
and processes these requests as a server, even though it's connected as a client to the simulated design acting as the server.

.. rubric:: dma.RAM

RAM used by ``DmaServicer``.

.. rubric:: nfb.CompRequest

Request transaction for ``NfbServicer``.

.. rubric:: nfb.NfbServicer

Processes requests on the simulator server, translating gRPC transactions into transactions for the PCIe driver.

.. rubric:: server.NfbDmaThreadedGrpcServer

This wrapper class encapsulates the aforementioned components, effectively turning a simulation object into a functional server.

cocotbext.nfb.ext.python
------------------------

.. rubric:: servicer.Servicer

This provides a concrete implementation for the ``libnfb`` extension's abstract interface, enabling its use directly from Python.

.. rubric:: servicer.Servicer.NdpQueue

Queues for packet transmission via the NDP interface, specific to the ``libnfb`` extension.

.. rubric:: servicer.Servicer.NdpQueueRx

Implementation of ``NdpQueue`` for RX transactions.

.. rubric:: servicer.Servicer.NdpQueueTx

Implementation of ``NdpQueue`` for TX transactions.
