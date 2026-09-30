.. _pcie_telemetry_mi:

PCIe telemetry
--------------

.. vhdl:autoentity:: PCIE_TELEMETRY_MI

.. _pcie_telemetry_probe:

Telemetry probe
^^^^^^^^^^^^^^^

.. vhdl:autoentity:: PCIE_TELEMETRY_PROBE

.. _pcie_telemetry_acc:

Telemetry counter memory
^^^^^^^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: PCIE_TELEMETRY_ACC

Software
^^^^^^^^

The component is read out by the ``nfb-pcie-telemetry`` tool from the OFM
Python package. The tool takes its whole layout from the configuration registers
of the component. The same binary therefore works with any number of PCIe
endpoints, DMA ports and MFB regions, without being rebuilt.

Installation
""""""""""""

The tool needs Python 3.11 or newer and the ``nfb`` module from the NDK-SW
repository. Install the OFM package from the ``python/ofm`` directory:

.. code-block:: bash

    python3.11 -m venv my-venv
    source my-venv/bin/activate
    source <ndk-fpga>/env.sh
    cd <ndk-fpga>/python/ofm
    pip install .

Use ``pip install -e .`` instead while you modify the tool itself. It installs
the package in editable mode.

Usage
"""""

Print the traffic measured over one second and exit:

.. code-block:: bash

    nfb-pcie-telemetry

Options:

.. code-block::

    -d, --device PATH      path to the NFB device (default: the first one)
    -i, --index N          index of the component in the DeviceTree (default: 0)
    -t, --interval SEC     length of the measured interval in seconds; 0 prints
                           the totals accumulated since the last clear
    -w, --watch            keep measuring and printing until interrupted
    -c, --clear            zero all counters and exit
    -j, --json             print the raw values as JSON instead of a table

With a non-zero interval the tool takes two snapshots and prints their
difference, so the report describes only that interval. With ``--interval 0``
it prints one snapshot, which is the traffic since the counters were last
cleared. The counters are wide enough (48 bits by default) that they do not
overflow in any practical measurement.

Example of the output:

.. code-block::

    PCIe telemetry - 1 endpoint(s), 1 DMA port(s) per endpoint
    ==========================================================
    Measured over 1.00 s

    PCIe endpoint 0
    ------------------------------------------------------------
    Link                      up
    Max payload size (MPS)    512 B
    Max read request (MRRS)   4096 B
    Extended tag (8-bit)      on
    10-bit tag                off
    Read completion boundary  64 B
    PTC tags free             118 (lowest 3)
    PTC storage FIFO free     640 words (lowest 96)

      PCIe clock 400.0 MHz, DMA clock 200.0 MHz

    Bus                 Used %  Words %  MFB stall %  MVB stall %  Used per region %    Gbps    Mpps    RD %   Avg B
    ------------------  ------  -------  -----------  -----------  -------------------  ------  ------  -----  -----
    PTC -> PCIe (RQ)    70.15   89.90    0.01         -            89.9 63.6 63.6 63.5  287.33  58.000  -      619
    PCIe -> PTC (RC)    44.67   49.40    0.00         -            44.8 44.7 44.6 44.6  182.99  34.000  -      673
    DMA0 -> PTC (UP)    66.45   66.90    22.70        13.90        66.7 66.2            68.04   58.000  25.86  198
    PTC -> DMA0 (DOWN)  45.45   48.60    0.80         0.30         45.5 45.4            46.54   34.800  -      167

      Why the PCIe transfer stopped (share of PCIe clock cycles)
        UP stream                              DOWN stream
        no free PCIe tag           13.60 %     MFB stalled towards DMA  8.40 %
        PCIe tag not ready          0.40 %     MVB stalled towards DMA  0.10 %
        no room for completions     0.00 %
        no completion header entry  0.00 %
        PCIe endpoint not ready     0.01 %

    Time spent low          of    none    <=1/8    <=1/2    rest
    ----------------------  ----  ------  -------  -------  ------
    PCIe tags               256   0.30    39.80    7.90     52.00
    PTC storage FIFO words  1024  0.00    21.00    27.00    52.00

Reading the report
""""""""""""""""""

The header of each endpoint shows the PCIe parameters negotiated with the host
(MPS, MRRS, extended and 10-bit tags, read completion boundary). It also shows
how many PTC tags and how many words of the PTC storage FIFO are free now, and
the lowest value each of them reached in the measured interval. Read that lowest
value first when the throughput is lower than expected. The histograms below
then say how long the resource stayed that low.

The clock frequencies are not read from a register. They are derived from the
cycle counters and the wall-clock length of the interval. They therefore also
serve as a sanity check that the measurement really covered the interval it
claims to.

Meaning of the columns:

Used %
    Occupancy of the bus, that is the sum of its region counters divided by the
    elapsed cycles times the regions of that bus. A region counts in a cycle in
    which the bus moved a word and a frame was open in that region. The whole
    region counts even when the frame ends in the middle of it, so this is the
    width the traffic occupied and not the width it filled.
Words %
    Share of clock cycles in which the bus moved a word, that is both SRC_RDY
    and DST_RDY were high. The denominator is every elapsed cycle, so 100 % says
    the bus never idled and was never stalled.
MFB stall %
    Share of clock cycles in which SRC_RDY was high and DST_RDY was low. What is
    left of 100 % after this column and *Words %* is the time the source had
    nothing to send.
MVB stall %
    The same for the MVB that carries the headers. The MVB has a handshake of
    its own, so it can be stalled while the MFB of the same bus runs. Buses
    without an MVB show a dash.
Used per region %
    The counter of one region divided by the elapsed cycles, region 0 first.
    Values that decrease towards the higher regions mean short transactions.
    Such transactions do not fill the whole word.
Gbps
    Rate of the transferred MFB items times the item size. A region that ends a
    frame contributes only the items up to its EOF_POS, so this is the length
    the traffic really had. The two sides of the PTC count different things.
    Between the DMA and the PTC the headers are carried on a separate MVB bus,
    so the DMA side buses carry payload alone. On the PCIe request bus the TLP
    header is part of the data stream and is counted in. The difference between
    the two sides is therefore the header overhead.
Mpps
    Transaction rate, millions of transactions per second. The DMA side buses
    have an MVB of their own, so their rate comes from the MVB items and holds
    every request including those that carry no payload. The PCIe side buses
    have no MVB and their frames are counted instead. The choice follows the
    bus, never the traffic, so it cannot change between two readings.
RD %
    Share of the requests that carry no payload. On the bus from the DMA module
    to the PTC these are the reads, and the writes are the remainder. Only that
    bus carries both kinds of request, so the others show a dash. A completion
    always has payload. On the PCIe side the header is part of the data stream,
    where these counters cannot tell a read from a write.
Avg B
    Transferred bytes divided by the frames on the MFB, that is the average
    length of one frame. *Mpps* counts requests rather than frames, so these two
    columns do not multiply out to *Gbps*.

The block at the bottom says how often the PTC had to stop a stream and why.
The *UP stream* column holds the reasons that stop the read requests on their
way to PCIe:

* the pool of free PCIe tags was smaller than what that cycle asked for,
* the tag FIFO had no tag ready, even though the pool was deep enough,
* the space left in the storage FIFO no longer covered the completions of the
  next group of requests,
* the Completion Header buffer of the PCIe Hard IP had no entry left for one
  more read,
* the PCIe endpoint itself stopped taking data.

The *DOWN stream* column holds the reasons that stop the completions on their
way to the DMA module. Both are measured before the split between the DMA ports.
One is measured on the MFB that carries the data. The other is measured on the
MVB that carries the headers. They become active before the *MFB stall %* of a
DOWN bus does. That column is measured on the far side of the clock crossing,
where the asynchronous FIFOs have already taken the burst. A DOWN reason is the usual cause of *no room
for completions* in the other column.

The first two reasons both come from the tag path and are counted apart,
because they ask for opposite changes. The first one means the completions do
not come back fast enough. It is answered by more tags or by shorter reads. The
second one is a property of the tag FIFO, not of the traffic. A released tag
counts as free as soon as it is written, but it reaches the read ports of that
FIFO only a few cycles later. The second reason therefore says nothing about how
many tags are left. It appears even when almost the whole pool is free. Use the
histogram below, not this line, to decide whether the tags are running out.

The third one needs care when it is read. The storage FIFO is not full when
this reason becomes active, because the space is only reserved ahead. The reason
therefore appears well before the histogram reaches its lowest band. The fourth
one covers a buffer inside the PCIe Hard IP for which no credit is counted. It
stays at zero on endpoint types that manage that buffer themselves. The last one is not a
counter of its own. It repeats the stalled cycles of the RQ bus, so that every
reason can be compared in one place.

Every reason is its own counter of cycles. It is divided by the elapsed PCIe
clock cycles of the same period as the rest of the report. The second line of
the header names that period: the measured interval, or everything since the
last clear.

The two histograms below them say how long each of the two resources that can
run out was short. The lowest value in the header cannot say this: four free tags
means the same whether it lasted one cycle or half a second.
Each histogram splits the time into four bands by how much of the resource was
free: none at all, up to an eighth, up to a half, and the rest. The bands are
narrowest near zero, because that is where the resource limits the transfer. The
``of`` column gives the capacity the bands are shares of. The band thresholds are
derived from that same number. Each band is a counter of cycles divided by the
elapsed PCIe clock cycles. Time spent in the lowest band is time in which the
PTC was close to a stall. A few percent there is worth reading even when the
average over the whole interval shows no shortage.

Both resources are counted on the PCIe clock. The reasons they cause are
observed on that same clock. The share of time in the lowest band and the share
of time the matching reason was active therefore describe the same cycles, and
the two can be compared.

If the counters could not keep up, the tool prints a ``LOST DELTAS`` or a
``READ-OUT OVERRUN`` warning at the top of the report. The numbers must not be
trusted then. The firmware keeps both flags set until software clears them. The
tool clears them at the start of every measured interval, so the warning
describes only the interval that was just printed. With ``--interval 0`` there
is no such start, so the flags describe everything since the last ``--clear``.

Python API
""""""""""

The same data is available to scripts:

.. code-block:: python

    from ofm.comp.pcie.telemetry import PcieTelemetry, format_report

    telemetry = PcieTelemetry()
    data = telemetry.read()          # takes a snapshot and returns a dict
    print(format_report(data, 1.0))  # or render it the same way the tool does

    telemetry.clear()                # zero all counters
    print(telemetry.status)          # busy, lost_deltas, readout_overrun

``read()`` first takes a snapshot in the firmware and only then reads it out, so
the returned values are consistent with each other even though reading them
takes many MI transactions.
