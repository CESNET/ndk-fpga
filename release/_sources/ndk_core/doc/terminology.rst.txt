.. _ndk_terminology:

NDK Terminology
---------------

This chapter explains frequently used terms.

Ethernet Port
^^^^^^^^^^^^^

In our terminology, the ``Ethernet Port`` corresponds to one physical network port, typically one optical cage (for example, QSFP28 or QSFP-DD).

Ethernet Lanes
^^^^^^^^^^^^^^

The term ``Ethernet Lanes`` refer to high-speed serial lines used in the physical layer of the Ethernet protocol.
Each type of Ethernet Port can use a different number of ``Ethernet Lanes`` (for example, QSFP28 uses 4, and QSFP-DD uses 8).

Ethernet Channel
^^^^^^^^^^^^^^^^

Each Ethernet Port can use a different number of high-speed serial lines (Ethernet Lanes), typically 4 or 8. Different Ethernet standards (like 100 GbE, 25 GbE,...) require one or more of these lanes. For port QSFP28, where there are 4 lanes running at 28 Gbps, 100 GbE standard would take up all 4 lanes together forming one ``Ethernet channel``. For another Ethernet standard like 25 GbE, one lane is enough. Using all 4 lanes, we would get 4 separate 25 Gigabit ``Ethernet channels``.

Ethernet Stream
^^^^^^^^^^^^^^^

An ``Ethernet Stream`` is a group of data interfaces (RX and TX) that transmits Ethernet packets from/to a selected number of Ethernet Channels.
In our platform, the number of ``Ethernet Streams`` typically corresponds to the number of Ethernet Ports.

DMA Stream
^^^^^^^^^^

An ``DMA Stream`` is a group of data interfaces (RX and TX) that transmits DMA packets from/to DMA module.
In our platform, the number of ``DMA Streams`` typically corresponds to the number of Ethernet Streams (and therefore Ethernet Ports).

DMA Channel
^^^^^^^^^^^

The DMA controller supports data transmission in each direction (RX and TX) in multiple independent queues, which in our terminology we refer to as ``DMA channels``.
