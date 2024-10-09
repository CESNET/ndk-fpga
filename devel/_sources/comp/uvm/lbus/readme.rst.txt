.. readme.rst: Documentation of the LBUS agent
.. Copyright (C) 2024 CESNET z. s. p. o.
.. Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

.. SPDX-License-Identifier: BSD-3-Clause

**********
LBUS Agent
**********

This agent is a low-level agent that is responsible for communication through the `Xilinx LBUS interface <https://docs.amd.com/v/u/2.4-English/pg203-cmac-usplus>`_.
This package, **uvm_lbus**, contains 2 agents. The TX agent sends low-level transactions to the DUT. The RX agent is responsible for correctly receiving low-level transactions sent by the DUT.

Sequence Item
==============

The following table shows properties in the *sequence_item* class.

.. code-block:: systemverilog

 rand logic [4*128-1 : 0] data;
 rand logic [4    -1 : 0] ena;
 rand logic [4    -1 : 0] sop;
 rand logic [4    -1 : 0] eop;
 rand logic [4    -1 : 0] err;
 rand logic [4*4  -1 : 0] mty;
 rand logic               rdy;

Sequences
=========

- *sequence_rx* is a common ready-generating sequence that internally uses the *uvm_common::rand_rdy*.
- *sequence_rx_stop* is a sequence with an asserted READY signal.
- *sequence_rx_fullspeed* is a sequence with a deasserted READY signal.

Sequence Libraries
==================

- *sequence_library_rx* contains: *sequence_rx*, *sequence_rx_stop*, *sequence_rx_fullspeed*.
- *sequence_library_rx_fullspeed* contains: *sequence_rx_fullspeed*.
