.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
.. SPDX-License-Identifier: BSD-3-Clause

.. _rate_limiter:

Rate Limiter
------------
The Rate limiter modifies the output speed according to the given configuration. The user is able to set the speed to anything from a constant rate to complex patterns needed for a specific application.

Operation
^^^^^^^^^
The component forwards the incoming data unchanged. Based on the values loaded to the configuration registers, it either lets the traffic flow through at full speed or slows the traffic down when the limit of the configured speed is reached. The user configures the output speed per each Interval (see the picture below). Each Interval can be configured to a different throughput speed via the corresponding register in the address space. The component loops over all configured Intervals, and after the last one, it starts again from the beginning. The component can limit the output speed based on the number of either bytes or packets.

There is a maximum amount of Intervals that can be configured, given by the INTERVAL_COUNT generic value. Each Interval consists of an INTERVAL_LENGTH number of Sections, where every Section lasts SECTION_LENGTH clock cycles. Within each Section, the incoming stream of data flows through the component at full speed until the configured speed limit is reached. Reaching the speed limit results in the flow being stopped completely which means the output speed is either full throughput or none. The configured speed only determines the proportion between these two states. At the end of the Section, the flow is restored (to full throughput) and the process is repeated in the next Section. The component detects that the limit is reached with a delay of a few clock cycles (depending on the limiting type), so the real amount of transmitted data won't be exactly the configured limit (constants are added to ensure staying under the limit). The SECTION_LENGTH value should be set to be sufficiently big to minimalize the consequence of these delays.

.. _timespace:
.. figure:: doc/timespace.svg
   :width: 100%
   :align: center

* INTERVAL_COUNT  = 8 intervals
* INTERVAL_LENGTH = 16 sections
* SECTION_LENGTH  = default 1000 ticks
* The arrows illustrate the moments when the flow of data is restored.
* The speeds are switched in the following order: 10Gb/s, 50Gb/s, 0Gb/s, 75Gb/s, 60Gb/s, 10Gb/s, ... and so on.

The component is set to transfer data at a constant speed of 100 Gb/s by default (@200MHz). If the speed value is given to the component directly via the generic OUTPUT_SPEED or otherwise, it has to be recalculated to bytes per section (or packets per section). Then the flow can be easily stopped when the number of transmitted bytes (or packets) reaches this value.


.. vhdl:autoentity:: RATE_LIMITER


Address space and configuration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
The component has several registers accessible through the MI interface that are used for its configuration.

+----------------+----------------------------------------------------+
| Address offset | Note                                               |
+================+====================================================+
|           0x00 | status register                                    |
+----------------+----------------------------------------------------+
|           0x04 | section length register                            |
+----------------+----------------------------------------------------+
|           0x08 | interval length register                           |
+----------------+----------------------------------------------------+
|           0x0c | interval count register (read-only)                |
+----------------+----------------------------------------------------+
|           0x10 | frequency (read-only)                              |
+----------------+----------------------------------------------------+
|           0x14 | 1st speed register                                 |
+----------------+----------------------------------------------------+
|           0x18 | 2nd speed register (INTERVAL_COUNT > 1)            |
+----------------+----------------------------------------------------+
|          . . . |                                                    |
+----------------+----------------------------------------------------+
|           0x?? | last speed register -> 0x14 + (INTERVAL_COUNT-1)*4 |
+----------------+----------------------------------------------------+

The data registers correspond with the information given in paragraph 'Generic parameters' and the status register fields are described below.

+----------------+---------------------------------------------------------------------------+
| SR Flag (bit)  | Note                                                                      |
+================+===========================================================================+
|              0 | idle flag (1 = idle, 0 = busy) (RO)                                       |
+----------------+---------------------------------------------------------------------------+
|              1 | configuration (W: 1 = start, 0 = stop) / is in configuration state (R)    |
+----------------+---------------------------------------------------------------------------+
|              2 | traffic shaping (W: 1 = start, 0 = stop) / traffic shaping is running (R) |
+----------------+---------------------------------------------------------------------------+
|              3 | auxiliary flag (WO)                                                       |
+----------------+---------------------------------------------------------------------------+
|              4 | reset pointer (reset pointer to the first configured speed) (WO)          |
+----------------+---------------------------------------------------------------------------+
|              5 | limiting (choose between byte limiting (0) and packet limiting (1) (RW)   |
+----------------+---------------------------------------------------------------------------+

Usage
^^^^^
The status register is mainly used as a control register. There are two types of flags that can be set: state and auxiliary. State flags ('idle flag', 'configuration' and 'traffic shaping') are used to switch between (or to signalize) the working modes of the component. Auxiliary flags ('reset pointer' and 'limiting') are used for minor changes in the behavior of the component. Use the 'auxiliary flag' to distinguish between these two groups (0 -> write state flags, 1 -> write auxiliary flags). To configure the component first set 'configuration' bit to 1 (and 'auxiliary flag' to 0). When in configuration state user can configure all of the data registers (except 'interval count' and 'frequency' registers which are read-only). To start the traffic shaping set 'traffic shaping' bit to 1 ('auxiliary flag' to 0 and when starting from configuration state also set 'configuration' bit to 0). Setting both flags ('configuration' and 'traffic shaping') to 1 at the same time will result in switching to configuration state due to the implemented priority. To write the auxiliary flags set 'auxiliary flag' to 1 and then set whatever auxiliary flags you need. By default when switched from traffic shaping state to idle state, the pointer to the active speed is not reset. So when switched back to traffic shaping, it will continue from the last speed where the run was interrupted. If this behavior is unwanted, the pointer has to be reset manually in idle state by setting the 'reset pointer' field in the table above to 1. Wheter to use byte limiting or packet limiting (take the values in speed registers as bytes per section or packets per section) is chosen by setting the 'limiting' flag accordingly (0 for byte limiting and 1 for packet limiting). If you're not using the provided software, keep an eye on preserving the auxiliary flags that you do not wish to change with the consequent write request (f. e. if you're using packet limiting - 'limiting' flag is set to 1 and then you wish to reset the pointer in idle state (setting both 'auxiliary flag' and 'reset pointer' to 1), make sure you also set the 'limiting' flag to 1, otherwise the limiting type will be overwritten with 0 resulting in switching to byte limiting).

Notes
^^^^^
* To simulate intervals of different lengths, set the same output speed to more intervals in a row.
* Remember to set consecutive speed registers. Upon encountering a gap in the form of an invalid (not set) speed register the component loops from the first speed again.
* When reading a speed register the most significant bit indicates whether the value was configured during the last configuration and is therefore valid (1) or not valid (0).
* The preferred way of interacting with the component is by using the provided software.
* The component starts in the IDLE state with traffic flowing through at full speed.
* When switched to configuration state speed registers get reset.
* The component supports the BE signal internally, although its usage is not needed anywhere in the current version.
* When using byte limiting in verification, output speed can (under some extreme circumstances) exceed the limit a little (packets on the border of two sections are counted as a whole to only one of them).

