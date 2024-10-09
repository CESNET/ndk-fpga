.. readme.rst: Documentation of AVST CRDT agent
.. Copyright (C) 2024 CESNET z. s. p. o.
.. Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

.. SPDX-License-Identifier: BSD-3-Clause

***************
AVST CRDT Agent
***************

This agent is a low-level agent that is responsible for communication through the `Intel Credit Control interface <https://www.intel.com/content/www/us/en/docs/programmable/683501/24-2-11-3-0/credit-control.html>`_.
This package, **uvm_avst_crdt**, contains 2 generic and 4 predefined agents. The RX agent sends credits to the DUT. The TX agent is responsible for the correct initialization.

Agents
======

The package contains RX and TX agents that can be parameterized with the **UPDATE_CNT_WIDTH** parameter.
The generic agents are configured with one parameter:

- UPDATE_CNT_WIDTH

Moreover, the package contains 4 agents with predefined parameter values:

- *agent_rx_hdr* with **UPDATE_CNT_WIDTH = 2**.
- *agent_rx_data* with **UPDATE_CNT_WIDTH = 4**.
- *agent_tx_hdr* with **UPDATE_CNT_WIDTH = 2**.
- *agent_tx_data* with **UPDATE_CNT_WIDTH = 4**.

Sequence Item
==============

The following table shows properties in the *sequence_item* class.

.. code-block:: systemverilog

    rand logic                          init;
    rand logic                          init_ack;
    rand logic                          update;
    rand logic [UPDATE_CNT_WIDTH-1 : 0] update_cnt;

Sequences
=========

- *sequence_rx* is a common credit-generating sequence.
- *sequence_rx_initializing* is responsible for correct initialization on the RX side.
- *sequence_tx_ack* is responsible for correct initialization on the TX side.

All these sequences have predefined *_hdr* and *_data* variants, just like agents do.
