.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. MVB agent and MVB interface
.. _uvm_mvb:

************
MVB agent
************

Interface
^^^^^^^^^

MVB interface is simple interface which is composed of signals below.

========      ===========            ================================================
Name          Width                  Description
========      ===========            ================================================
DATA          WORD_WIDTH             This signal containts data to be transferred.
VLD           ITEMS                  For each item in ``DATA`` there is one valid bit. If the bit is HIGH then that item is valid.
SRC_RDY       1                      Source if ready when this signal is HIGH.
DST_RDY       1                      Destination if ready when this signal is HIGH.
========      ===========            ================================================

The  ``ITEMS`` and ``ITEM_WIDTH`` are parameters and they must be greater then 0.
The ``WORD_WIDTH`` is local parameter and its value is calculated my multiplying parameters ``ITEMS`` and ``ITEM_WIDTH``.

The interface is used for both RX nad TX. For each direction there is dut and driver modport.
Also there is one modport for monitor. This modport is used for both RX and TX.

There are asserts to check correct settings and functionality of interface.

Sequence item
^^^^^^^^^^^^^
Sequence item have same signals as interface accept for ``DATA``. In the ``DATA`` is saved all items in the array.
There is ``ITEMS``'s logic vector items with width of ``ITEM_WIDTH``.

All of those signals are randomized. There also are overridden UVM functions("do_compare", "do_copy" and "convert2string").

Sequence
^^^^^^^^
There is ``req`` which is instance of sequence_item. There are 2 unsigned integers ``max_transaction_count`` and ``min_transaction_count``.
Last variable is randomized ``transaction_count``. This variable is randomized in range of <``max_transaction_count``, ``min_transaction_count``>.

There are 2 sequences. One for RX and one for TX. This is because TX, and RX behave differently.
Signal ``SRC_RDY`` must remain rised until the ``DST_RDY`` is also rised. This behavior must be simulated on the RX side.

Because of this there is one bit variable ``next_action``. This bit decide on contents of actual ``req`` based on previous sequence item.

Driver
^^^^^^
The driver gets sequence_item from sequence and assign corresponding signals to interface.

Because of behaviour described above there are also 2 drivers. One for RX and one for TX. The RX driver have to also create response and sand it back to sequence.

Monitor
^^^^^^^
Monitor just waiting for monitor clocking block and than sample values at interface. And at the end he write this sample to the analysis port.

Config
^^^^^^
In the config 2 variables. First is ``active`` that decides if the driver and sequencer will be created. And the second one is ``interface_name``.

Agent
^^^^^
There are also 2 agents. Agent only connect everything together.
