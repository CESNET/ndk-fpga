.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Logic Vector Array agent
.. _uvm_logic_vector_array:

************************
Logic Vector Array agent
************************

The main task of this agent is to generate a field of logic vectors that can be sent to the DUT through a lower-level agent. This agent does not contain a driver because it is a higher-level agent.
However, it connects all components like the driver, monitor, etc., together. It has its own configuration object which contains one parameter: active (the agent is active when it is set, else it is passive).
When the agent is active, a sequencer is created. When it is passive, only a monitor is created.

Logic Vector Array sequence item
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A sequence item contains only one randomizable item.

- ``logic[ITEM_WIDTH-1 : 0] data[]`` sequence_item randomizable variable

====================           ========================================================================
Function                        Description
====================           ========================================================================
- ``do_copy``                  Is used for copying of the transaction.
- ``do_compare``               Is used for comparing data of two transactions.
- ``convert2string``           Is used for printing the whole transaction.
- ``convert2block``            Is used for printing the whole transaction which is divided into blocks.
====================           ========================================================================


Logic Vector Array monitor
^^^^^^^^^^^^^^^^^^^^^^^^^^

Logic Vector Array monitor is a basic class used to monitor traffic.
This is only a simple monitor which creates an analysis port and a sequence item
and must be subclassed to a particular lower-level interface.

    See, for example, the logic_vector_array_mfb environment of Logic Vector Array to MFB conversion.

Logic Vector Array Sequence
^^^^^^^^^^^^^^^^^^^^^^^^^^^

This package contains some interesting predefined sequences. Sequences generate N random transactions.
The number of transactions is randomly selected when the sequence is randomized. Transactions contain a randomizable
byte array. The major difference between the sequences is the boundary of the randomized size of a byte array.
Every sequence has its own setting which sets a boundary for the randomization process. The following table shows
a simplified description of these sequences. It describes the properties of byte arrays in transactions.


=====================           =============================================================================
Sequence                        Description
=====================           =============================================================================
sequence_simple                 the size of the byte array is randomly distributed by a uniform distribution,
sequence_simple_const           the size of the byte array is the same for all transactions in the sequence,
sequence_simple_gauss           the size of the byte array is randomly distributed by a normal distribution,
sequence_simple_inc             the size of the byte array is increased for every generated transaction,
sequence_simple_dec             the size of the byte array is decreased for every generated transaction
=====================           =============================================================================


The last sequence is the ``sequence_lib``, which picks N random sequences from the list above
and runs them consecutively on the sequencer


Sequence configuration
^^^^^^^^^^^^^^^^^^^^^^

The configuration object `config_sequence` contains a single configuration function.

=========================  =======  ===================================
Function                   Type     Description
=========================  =======  ===================================
array_size_set(min, max)   [bytes]  Set minimum and maximum array size
=========================  =======  ===================================

.. code-block:: systemverilog

    sequence_lib seq;

    seq = sequence_lib::type_id::create("seq");
    seq.cfg = new();
    //set maximum and minimum packet size
    seq.cfg.array_size_set(64, 128);


