.. _mfb_discarder:

MFB Discarder
-----------

MFB Discarder discards selected packets, consisting of MFB and associated MVB words, on the input interface.
It is controlled by the ``RX_MVB_DISCARD`` input port / flag.
Packets with ``RX_MVB_DISCARD`` set to 1 are discarded (dropped) by the component, while packets with ``RX_MVB_DISCARD`` set to 0 are passed to the output interface.

Architecture
^^^^^^^^^^^^

The architecture utilizes an MFB splitter with 2 output ports, with the ``RX_MVB_DISCARD`` connected to the ``RX_MVB_SWITCH``. This signal thus selects the output port of the switch for each packet. The first switch's output port is connected to the output port of the Discarder component, which is where the packets with ``RX_MVB_DISCARD`` set to 0 end up. The second switch's output port is not connected (ready signal are tied to 1) and is used for the actual discarding.

.. vhdl:autoentity:: MFB_DISCARDER
