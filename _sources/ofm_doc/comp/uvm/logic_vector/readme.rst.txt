.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Logic vector agent
.. _uvm_logic_vector:


******************
Logic vector agent
******************

The main task of this agent is to generate field of logic vector[ITEM_WIDTH-1:0] which can be sent to DUT through the lower level agent. This agents does not contains a driver because it is higher level agent.
Agent is used for connecting of all components (driver, monitor,...). Agent has his own configuration object which contains one parameter active (when is up then agent is active in other way is passive).
When agent is active then sequencer is created. When is passive then only monitor is created.

Logic Vector Array sequence item
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Sequence item contains only one randomizable item.

- ``logic [ITEM_WIDTH-1:0] data[]`` sequence_item randomizable variable


- ``do_copy`` is used for copying of the transaction.
- ``do_compare`` is used for comparing data of two transactions.
- ``convert2string`` is used for printing whole transaction.



Logic Vector Array monitor
^^^^^^^^^^^^^^^^^^^^^^^^^^

Logic vector array monitor is base class used for monitoring of traffic.
This is only simple monitor which creates analysis port and sequence item
and must be subclassed to particular lower level interface.

    See the ligc_vector_array_mfb environment for example of ligic vector Array to MFB conversion.

Logic Vector Array Sequence
^^^^^^^^^^^^^^^^^^^^^^^^^^^

This package contains some interesting predefined sequences. Sequences generate N random transactions.
The number of transactions is randomly selected when the sequence is randomized. Transactions contain a randomizable
logic_vector array. The major difference between the sequences is the boundary of the randomized size of a logic vector array.
Every sequence has its setting which set a boundary for randomization. The following table shows
a simplified description of those sequences. The description describes properties of logic vector array in transactions.


==========================           ======================================================
Sequence                             Description
==========================           ======================================================
sequence_simple                      size of logic vector array is randomly distributed by uniform distribution
sequence_simple_const                size of logic vector array is same for all transactions in sequence
sequence_simple_gauss                size of logic vector array is randomly distributed by normal distribution
sequence_simple_inc                  size of logic vector array is increasing in every generated transactions
sequence_simple_dec                  size of logic vector array is decreasing in every generated transactions
==========================           ======================================================


The last sequence is ``sequence_lib``, which picks N random sequences from the list above
and run consecutively run then on sequencer


Sequence configuration
^^^^^^^^^^^^^^^^^^^^^^

Configuration object `config_sequence` contain one configuration function.

=========================  ======================  ======================================================
Function                   Type                    Description
=========================  ======================  ======================================================
array_size_set(min, max)   [bytes]                 Set minimum and maximum array size.


.. code-block:: systemverilog

    sequence_lib seq;

    seq = sequence_lib::type_id::create("seq");
    seq.cfg = new();
    //set maximum and minimum packet size
    seq.cfg.array_size_set(64, 128);

