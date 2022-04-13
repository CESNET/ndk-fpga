.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Byte Array agent
.. _uvm_byte_array:

****************
Byte Array agent
****************
The main task of this agent is generate field of bytes which is then processed in low level agent. This agents does not contain driver because it is high level agent.
Agent is used for connecting of all components (driver, monitor,...). Agent has his own configuration object which contains one parameter active (when is up then agent is active in other way is passive).
When agent is active then sequencer is created. When is passive then only monitor is created.

Byte Array sequence item
------------------------
Sequence item contains randomized byte data field which is cut to smaller chunks in low level agent.

There are three methods:

- ``do_copy`` is used for copying of the transaction. 
- ``do_compare`` is used for comparing data of two transactions.
- ``convert2string`` is used for printing whole transaction.

Byte Array monitor
^^^^^^^^^^^^^^^^^^
Byte Array monitor is used for monitoring of traffic. There is only easy monitor which create analysis port and sequence item.

Byte Array Sequence
^^^^^^^^^^^^^^^^^^^
Byte Array Sequence is used for generation of transaction. NUMBER_OF_TRANSACTION say how many transactions will be generate. Length of transaction is generate in range from MIN_LENGTH to MAX_LENGTH. Data of this sequence are randomized.
