.. _axi2avmm_ddr_bridge:


AXI-AVMM DDR Bridge
===================

Converts an Avalon-MM slave interface into an AXI4 master interface, so an NDK
memory master can talk to a DDR or HBM controller. The Avalon-MM side is word
addressed and the AXI side is byte addressed; the bridge multiplies the word
address by the word size in bytes and passes the data straight through, so both
sides must use the same data width.

Avalon-MM defines the address and the burst count only on the first beat of a
burst. The bridge latches both when a burst starts and uses the latched copies
for the rest of it, which is what lets the AXI address phase outlive the Avalon
burst that produced it.

The component is verified by a cocotb testbench in the ``cocotb`` directory,
which drives the Avalon-MM side, terminates the AXI side with a slave memory and
watches both with a passive AXI4 protocol checker. Run it with ``make`` for
QuestaSim or ``make TARGET=nvc-sim`` for NVC.

.. vhdl:autoentity:: AXI2AVMM_BRIDGE
