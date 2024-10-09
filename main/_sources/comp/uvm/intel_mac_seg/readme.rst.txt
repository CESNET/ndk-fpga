.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. intel mac seg agent
.. _uvm_intel_mac_seg:

*************
Intel MAC SEG
*************

This agent is a low-level agent that is responsible for communication through Intel MAC SEG. It is commonly used for ethernet communication.
The **intel_mac_seg_if** interface has one parameter, **SEGMENTS**, which represents a number of segments. There are two agents for Rx and Tx communication.
The component is commonly used with the uvm_logic_vector_array when the **uvm_logic_vector_array::sequence_item** has to be converted to the **uvm_intel_mac_seg::sequence_item**.


Sequence item
^^^^^^^^^^^^^

 - rand logic [64-1:0] data[SEGMENTS];
 - rand logic          inframe[SEGMENTS];
 - rand logic [3-1:0]  eop_empty[SEGMENTS];
 - rand logic          fcs_error[SEGMENTS];
 - rand logic [2-1:0]  error[SEGMENTS];
 - rand logic [3-1:0]  status_data[SEGMENTS];
 - rand logic          valid;
 - rand logic          ready;


Sequence
^^^^^^^^

There are two sequences. The one for RX is not commonly used. It doesn't generate truly valid frames. Better is to use the **uvm_logic_vector_array_intel_mac_seg::env**
environment. The Tx one generates a ready signal for the Tx agent.


Config
^^^^^^

The config contains two variables. The **active** decides whether the agent drives the interface or only observes the interface.
The **interface_name** variable represents the name under which is interface stored in a database.

 -   uvm_active_passive_enum active;
 -   string interface_name;
