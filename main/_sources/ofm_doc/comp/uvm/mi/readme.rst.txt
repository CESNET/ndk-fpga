.. readme.rst: Documentation of reset agent 
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause


********
MI agent
********
This package containts two UVM vrification agents which generate transaction to interface :ref:`MI bus specification<mi_bus>`. Slave agent is connet to slave DUT port. Master agent is connected to master DUT port.
Both agents have three class parameters. ``DATA_WIDTH`` , ``ADDR_WIDTH`` and ``META_WIDHT``. ``META_WIDTH`` has default value set to 0.


.. image:: ../docs/MI_agent.svg
    :align: center
    :width: 50 %


Sequence_item
^^^^^^^^^^^^^^^^^^
There is two sequence item. First sequence_item_request is for generating request and second sequence_item_response is for response.

Sequence_item_request

========     ========      ================================================
Name         Random        Description
========     ========      ================================================
addr         yes           Requested adress. Variable is logic vector widht ``ADDR_WIDTH``
meta         yes           Metadata. Variables is logic vector width ``META_WIDTH``
be           yes           Byte enable for reading or writing data. Variable is logic vector width ``DATA_WIDTH/8``
wr           yes           Write requeste. It cannot be assert when signal rd is assert
dwr          yes           Written data. Variable is logic vector width ``DATA_WIDTH``
rd           yes           Read request. It cannot be sserted when signal wr is asserted
ardy         no            Driver send response in this signal if reqeust have been accepted DUT.
========     ========      ================================================


Sequence_item_response

========     ========     ================================================
Name         Random       Description
========     ========     ================================================
drd          yes          Responded data. Variables is logic vector width ``DATA_WIDTH``
drdy         yes          Assert when variable drd is valid.
ardy         yes          accepting request
========     ========     ================================================


Slave agent use only sequence_item_request with extension of ardy. which is set to 1 when request is accepted by DUT.

Master agent use two sequence_item. Sequence_item_request and sequence_item_response. When response is generated and send to DUT driver response with sequence_item_request.
Master driver cannot reply in same clock thick as response. This create hole in functional verification which should be covered in future implementation. But it made comunication protocal
more complicated and depends on clock. Currenty comunication between master_driver and master_sequence work like. Firstly is send response which would be exposted to interface.
After clock event master driver read request from interface and send it to sequence. This mean response have to be send to driver earlier that request is known.
This would be improve in future.


There is five prepared sequences for slave agent.

=============================        ================================================
Name                                 Description
=============================        ================================================
sequence_slave                       generate random 10-200 mi transactions
sequence_slave_same_addr             generate random 10-200 mi transaction to random pick adrres
sequence_slave_incr_addr             genearte random 10-200 mi transaction. Ewery transaction is on different addres. When sequence is randomized then is randomly          pick first adress, random increment size and if sequence increment or decrement adress.
sequence_slave_slave_burst           generate random 10-200 mi transaction. Sequence randomly chose burst mode. There is four burst mode (NO_OPERATION, ONLY READ, ONLY WRITE, RANDOM READ WRITE).
sequence_slave_library               Run random number of mi slave sequence's on mi mequencer. The number of sequence's is in bounds from 100 to 500."
=============================        ================================================


There is four prepared sequences for master agent. Sequence_master contain taks set_rd which read response and check if reset have been asserted. Then add request to sequencer if there is.
If reset is set then all request is delete from sequencer.

========================    ================================================
Name                        Description
========================    ================================================
sequence_master             generate random 10-200 mi transactions
sequence_master_burst       generate random 10-200 mi transaction to random pick adrres. When sequece is randomized then is randomly pick bust mode. (NO ARDY and DRDY, ONLY ARDY, ONLY DRDY, ARDY And DRDY). DRDY is generated only when enought reqeusted for reading have beend received.
sequence_master_max         genearte random 10-200 mi transaction. Ardy is asserted always. Drdy have one clock thick delay. this is implementation limitation.
sequence_slave_library      Random run mi sequence_slave sequence 100 - 500 on mi sequencer.
========================    ================================================



