.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
.. SPDX-License-Identifier: BSD-3-Clause

.. _rate_limiter:

Rate Limiter
------------

The Rate limiter modifies the output speed according to the given configuration.
The user can set the speed to anything, from a constant rate to complex patterns, as needed for the specific application.

Operation
^^^^^^^^^

The component forwards the incoming data unchanged.
Based on the values loaded to the configuration registers, it either lets the traffic flow through at full speed or slows the traffic down when the limit of the configured rate is reached.
The user configures the output speed per each Interval (see the picture below).
Each Interval can be configured to a different throughput speed via the corresponding register in the address space.
The component loops over all configured Intervals, and after the last one, it starts again from the beginning.
The component can limit the output speed based on the number of either bytes or packets.

A maximum amount of Intervals can be configured, given by the INTERVAL_COUNT generic value.
Each Interval consists of an INTERVAL_LENGTH number of Sections, where every Section lasts SECTION_LENGTH clock cycles.
Within each Section, the incoming data stream flows through the component at full speed until the configured speed limit is reached.
Reaching the speed limit stops the flow completely, meaning the output speed is either full throughput or none.
The configured speed only determines the proportion between these two states.
At the end of the Section, the flow is restored (to full throughput), and the process is repeated in the next Section.
The component detects that the limit is reached with a delay of a few clock cycles (depending on the limiting type), so the actual amount of transmitted data won't be exactly the configured limit.
This is solved by adding constants to the current amount of transferred data to ensure the limit is not surpassed.
Unfortunately, this approach is not ideal, and some configuration restrictions must be met for the component to function correctly (see the :ref:`Usage section <usage>`).

.. _timespace:
.. figure:: doc/timespace.svg
    :width: 100%
    :align: center

* INTERVAL_COUNT  = 8 intervals
* INTERVAL_LENGTH = 16 sections
* SECTION_LENGTH  = default 1000 ticks of the clock signal
* The arrows illustrate the moments when the flow of data is restored.
* The speeds are switched in the following order: 10Gb/s, 50Gb/s, 0Gb/s, 75Gb/s, 60Gb/s, 10Gb/s, ... and so on.

The component's default configuration is set to transfer data at full speed.
Whether the speed value is given to the component directly via the generic OUTPUT_SPEED or configured after the start, it has to be recalculated to bytes per Section (or packets per Section).
See the Speed conversions and Adjusting Section Length sections below.
This way, any conversions in the firmware can be omitted, which simplifies the logic.


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

The data registers correspond with the information given in paragraph 'Generic parameters', and the status register fields are described below.

+----------------+---------------------------------------------------------------------------+
| SR Flag (bit)  | Note                                                                      |
+================+===========================================================================+
|              0 | idle flag (1 = idle - default, 0 = busy) (RO)                             |
+----------------+---------------------------------------------------------------------------+
|              1 | configuration (W: 1 = start, 0 = stop) / is in configuration state (R)    |
+----------------+---------------------------------------------------------------------------+
|              2 | traffic shaping (W: 1 = start, 0 = stop) / traffic shaping is running (R) |
+----------------+---------------------------------------------------------------------------+
|              3 | auxiliary flag (WO)                                                       |
+----------------+---------------------------------------------------------------------------+
|              4 | reset pointer (W: 1 = reset pointer to the first configured speed) (WO)   |
+----------------+---------------------------------------------------------------------------+
|              5 | limiting type (W: 1 = packet limiting, 0 = byte limiting - default) (RW)  |
+----------------+---------------------------------------------------------------------------+

.. _usage:

Usage
^^^^^

**Intro**

The status register is also used as a control register.
By setting its bits (flags), the user can change the working modes of the Rate Limiter and its settings.
Two types of flags can be set: state and auxiliary.
State flags indicate/set the working mode of the component:

- IDLE mode (default, no limiting applied; it is the full throughput mode),
- CONFIGURATION mode (in which the user can change parameters such as the Section Length, Interval Length, and the Output Speed(s)), and
- RUN mode (also the limiting mode, where traffic flows through at the configured speed(s)).

The auxiliary flags (RESET POINTER and LIMITING TYPE) do not directly affect the traffic flow.
To distinguish between these two types of flags, use the AUXILIARY FLAG as follows: set it to 0 to change the state flags (i.e., leave it as it is) and to 1 to change the auxiliary flags.

**The modes**

Let's run through an example to make it more straightforward.
The component starts in the IDLE state (Status register: ``0b000001``).
The values of the other registers (Section Length register, Frequency register, etc.) will have default values set by the generic values of the component.
If this is good enough, you can transition straight to the RUN mode by writing ``0b000100`` to the Status register.

Otherwise, if you need to change some of the other-than-Status registers, you must first switch to the CONFIGURATION mode (``0b000010`` -> Status register).
Here, you can change the output speeds for all intervals (max number of intervals set by the INTERVAL_COUNT parameter at the build phase).
Multiple intervals might be useful when attempting some traffic-shaping mechanism.
You never have to set a value to all of the Speed registers.
Each of the Speed registers is automatically validated when a value is written to it (the Speed register's MSB is set to '1' - you can notice this when reading it back).
During the RUN mode, when the last Speed register with a valid speed is reached, it loops back to the first Speed register and starts all over again.
This implies that you must set consecutive Speed registers because the first invalid Speed register will restart the loop (e.g., even speed 0 must be written to be valid).

Often, you may want just some simple throughput limiting at a steady speed.
Then, you only use the first Speed register (at the address offset 0x14).
You can ignore the Interval Length register and, in most cases, also the Section Length register.

**Limitation of the Speed register**

In one particular case, you must pay attention to the Section Length register.
Here, we return to the constants mentioned above that are added to the currently accumulated data (to avoid surpassing the configured speed).
But setting the Speed register value less or equal to the value of the constant will result in no throughput at all!
Do not despair, there is a workaround available.
You can extend the Section Length and change (increase) the Speed accordingly.
Before understanding how that might work in practice, let's first look into configuring the Speed.

**Speed conversions**

Configuring the Speed is a bit tricky because the value of the Speed register is in Bytes (or Packets) per Section, and the length of the Section (see the Section Length parameter) is in clock ticks.
Hence, the desired speed, e.g., in Gbps, must be converted before being written into the Speed register.
There are conversion functions in the provided script (./sw/rate_limiter.py) that you may take inspiration from:

- for conversion from Gbps to Bytes per Section (Bscn), there is the ``conv_Gbs2Bscn`` function
- for conversion from Bscn to Gbps, there is the ``conv_Bscn2Gbs`` function
- for conversion from packets per second (pps or Ps) to packets per Section (Pscn), there is the ``conv_Ps2Pscn`` function
- for conversion from Pscn to pps, there is the ``conv_Pscn2Ps`` function

However, the basic formula is: Xscn = Xps [X/seconds] / (Frequency [Hz] / SectionLength [clock ticks]), where the ``X`` (also in Xscn and Xps) represents Bytes or Packets.

.. note::
    When ``Xps`` is in bits (Gbps, Mbps, ...), it is necessary to divide it by 8 to get Bytes!
    Or you can convert the speed into Bytes per second upfront.

**Adjusting Section Length**

The adjustment of the Section Length is necessary in cases when low output speeds are required.
These are the minimum values (after conversion) the Speed register can have:

- pps limiting: ``MinimumSpeed = 1 + MFB_REGIONS*1`` packets per Section (100G: MFB_REGIONS = 1, 400G: MFB_REGIONS = 4),
- bps limiting: ``MinimumSpeed = 1 + 3*MFB_WORD_WIDTH/8`` Bytes per Section (100G: MFB_WORD_WIDTH = 512b, 400G: MFB_WORD_WIDTH = 2048b)

.. warning::
    Setting the value of the Speed register below the mentioned limits causes the traffic to halt.

The formula to meet the condition is the following: Xps [X/seconds] / (Frequency [Hz] / SectionLength [clock ticks]) >= MinimumSpeed.
The left side of this equation is the value of the Speed register (Xscn), and the MinimumSpeed value on the right side is the constant defined above.
The goal is to determine whether the Section Length is large enough and, if not, increase it and use the new value to calculate the Speed register value.
A simple solution follows:

.. code-block::

    if (SectionLength < MinimumSpeed * Frequency / Xps): # if this condition is met, the Speed will be below the limit
        SectionLength = (MinimumSpeed * Frequency / Xps) # sets the Section Length to the smallest possible value - the Speed register value will be the MinimumSpeed

This has to be done before setting the Speed register value.
Following this, you should convert your desired speed into the Xscn format using this (potentially new) value of Section Length.

.. code-block::

    Bscn = ceil((bps/8) / (Frequency/SectionLength)) # The basic formula mentioned in the "Speed conversions" section above.

**Types of the Auxiliary flags**

As previously mentioned, there are two Auxiliary flags in the Status register.
Bit number four is the flag allowing the user to reset the pointer to the current Speed register manually.
It is useful only when using multiple intervals.
In the default state, after stopping the traffic flow (returning to IDLE or CONFIGURATION mode), the pointer to the current Speed register does not change.
This flag (which must be set only in the IDLE state) resets the pointer to the first Speed register.

Bit number five switches between the types of limiting.
When this bit is 0 (default), the output speed is limited according to bps - the value of the Speed register is perceived to be in Bytes per Section.
When it is set to 1, the output speed is limited according to pps, and the value of the Speed register is perceived to be in Packets per Section.
This bit can be changed independently on its current state, but be aware of its impact in the RUN state - suddenly, the Speed register will have the same value but in different units (Bscn <-> Pscn).

**Setting the Auxiliary flags**

To set the auxiliary flags, set the AUXILIARY FLAG (bit number three) to 1 and with that (in the same write request) whatever auxiliary bits you need.
Both Auxiliary bits are always set simultaneously, so for data consistency, either store their values (keep them in the memory) or read their values before every change.
For example, if you're using packet limiting - the LIMITING TYPE flag is set to 1 - and then you wish to reset the pointer in the IDLE state, make sure you also set the LIMITING TYPE flag to 1 because this single write request will overwrite both bits.

Notes
^^^^^

* To simulate intervals of different lengths, set the same output speed to more Intervals in a row.
* Remember to set consecutive speed registers. Upon encountering a gap in the form of an invalid (not set) speed register, the component loops from the first speed again.
* When reading a speed register, the most significant bit indicates whether the value was configured during the last configuration and is, therefore, valid (1) or not valid (0).
* The Speed registers are reset When switched to the IDLE or CONFIGURATION state.
* The preferred way to interact with the component is using the provided software (Python script).
* The component supports the BE signal internally, although its usage is not needed anywhere in the current version.
* When using 'byte limiting' in the verification, the output speed can (under some extreme circumstances) exceed the limit a little (packets on the border of two sections are counted as a whole to only one of them).

