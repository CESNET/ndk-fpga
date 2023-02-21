.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. UVM MI
.. _uvm_mi:

MI agent
********
This package contains two UVM verification agents which generate transactions to the :ref:MI<mi_bus> interface. The slave agent is connected to the slave DUT port but acts as the master of this communication (the slave agent generates the requests for the DUT). The master agent is connected to the master DUT port but acts as the slave of this communication (it accepts the requests from the DUT).
Both agents have three class parameters. ``DATA_WIDTH`` , ``ADDR_WIDTH`` and ``META_WIDTH``. ``META_WIDTH`` has default value set to 0.

.. image:: ../docs/MI_agent.svg
   :align: center
   :width: 50 %

Sequence_item
^^^^^^^^^^^^^^^^^^
There are two sequence items. The sequence_item_request is for generating requests, and the sequence_item_response is for responses.

Sequence_item_request

======== ======== ================================================
Name     Random   Description
======== ======== ================================================
addr     yes      Requested address. Variable is the logic vector width ``ADDR_WIDTH``.
meta     yes      Metadata. Variable is the logic vector width ``META_WIDTH``.
be       yes      Byte enable for reading or writing data. Variable is the logic vector width ``DATA_WIDTH/8``.
wr       yes      Write request. It cannot be asserted when signal rd is asserted.
dwr      yes      Written data. Variable is the logic vector width ``DATA_WIDTH ``.
rd       yes      Read request. It cannot be asserted when signal wr is asserted.
ardy     no       Driver sends a response in this signal if the request has been accepted DUT.
======== ======== ================================================

Sequence_item_response

======== ======== ================================================
Name     Random   Description
======== ======== ================================================
drd      yes      Responded data. Variable is the logic vector width ``DATA_WIDTH``.
drdy     yes      Assert when variable drd is valid.
ardy     yes      Acception of the request.
======== ======== ================================================

The slave agent uses only the sequence_item_request with the extension of ardy, which is set to 1 when the DUT accepts a request.
The master agent uses two sequence items: sequence_item_request and sequence_item_response.
When a response is generated and sent to the DUT, the driver responds with a sequence_item_request.
The master driver cannot reply at the same clock cycle as the response.
This creates a hole in the functional verification which should be fixed in the future.
But it made communication protocol more complicated and depended on the clock.
Currently, the communication between master_driver and master_sequence works like this.
First, the master_driver sends a request to the master_sequence to get an "invalid" response that is not sent to the DUT, it just starts off the communication between them.
The sequence replies with a request that is actually the first response for the DUT MI master.
This means that a response must be sent to the driver before the request is known.
This would be improved in future.

There are six prepared sequences for the slave agent.

============================= ================================================
Name                          Description
============================= ================================================
sequence_slave                generate random 10-200 MI transactions
sequence_slave_same_addr      generate random 10-200 MI transactions to random addresses
sequence_slave_incr_addr      generate random 10-200 MI transactions. Every transaction is to a different address. When the sequence is randomized, then the first address is random, the increment/decrement size, and whether the address is incremented or decremented.
sequence_slave_slave_burst    generate random 10-200 MI transactions. Sequence randomly selects burst mode. There are four burst modes (NO_OPERATION, ONLY READ, ONLY WRITE, RANDOM READ WRITE).
sequence_slave_sim            generate user-defined MI transactions. There are three tasks, mi_write (for MI write transactions), mi_read (for MI read transactions), get_rsp (to get MI read response) and create_sequence_item (A virtual task where the user can define a set of custom MI transactions).
============================= ================================================

There are four prepared sequences for the master agent.
A sequence_master contains a task set_rd which reads the response and checks if reset has been asserted.
Then it adds a request to the sequencer if there is one.
If reset is set, then all requests are deleted from the sequencer.

======================== ================================================
Name                     Description
======================== ================================================
sequence_master          generate random 10-200 MI transactions
sequence_master_burst    generate random 10-200 MI transaction to random addresses. When the sequence is randomized, then a burst mode is randomly selected. (NO ARDY and DRDY, ONLY ARDY, ONLY DRDY, ARDY and DRDY). DRDY is generated only when enough requests for reading have been received.
sequence_master_max      generate random 10-200 MI transaction. Ardy is always asserted. Drdy has one clock cycle delay. This is the implementation's limitation.
sequence_slave_library   Randomly run MI sequence_slave 100 - 500 sequences on the MI sequencer.
======================== ================================================