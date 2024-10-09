.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. PMA interface
.. _uvm_pma:

************
PMA agent
************

Agent is used for connecting of all components (driver, monitor,...). Agent has his own configuration object which contains two parameters: active (when is up then agent is active in other way is passive) and interface which say name of the interface that is used.
When agent is active then sequencer and driver are created amd connected to interface. When is passive then only monitor is created.

PMA interface
-------------
PMA (Physical Medium Attachment) bus is proprietary interface which is connected to tranascievers. Main task of this interface is took data from encoder, scramble them and send it to tranasciever. There could be two types of data (depends on header), control data or usable data. On this interface are encoded data from encoder, this data could have this formats:

- ``IDLE`` this format contains: first eight bits which define type of frame (type ``IDLE``) and others zeros which specify space between frames.
- ``START`` this format contains: first eight bits which define type of frame (type ``START``) and others bytes are data bytes.
- ``DATA`` this format contains only data bytes and don't have type.
- ``TERMINATE`` this format contains: eight bits which define type of frame (type ``TERMINATE``), position of type depends on amount of data which are sended with terminate. So there in the first place there are data bytes (amount depends on number of data valid bytes), then type and in last there are zeros (space between frames).

PMA bus description
^^^^^^^^^^^^^^^^^^^
PMA bus has these 5 ports which will be described below.

Generics
^^^^^^^^
===================  =============  ============  =====================================================
Name                 Type           Default       Description
===================  =============  ============  =====================================================
DATA_WIDTH           natural        32            Data word width in bits.
===================  =============  ============  =====================================================

Ports
^^^^^
=============  ===  ==================     ======================================================
Name           Dir  Dimension              Description
=============  ===  ==================     ======================================================
DATA           IN   DATA_WIDTH             Encoded and scrambled data from PMA.
DATA_VLD       IN   DATA_WIDTH             Data valid
HDR            IN   2                      Header from PMA, valid states are 01 (control block) and 10 (data block).
HDR_VLD        IN   1                      Header valid, this port is valid once per two clocks.
BLOCK_LOCK     IN   1                      This port say that transmiting has started.
=============  ===  ==================     ======================================================

PMA sequence item
-----------------
Sequence item contains basic ports from interface. All signals which are in sequence item are randomized.
There are three methods:

- ``do_copy`` is used for copying of the transaction.
- ``do_compare`` is used for comparing data of two transactions.
- ``convert2string`` is used for printing whole transaction.

PMA monitor
-----------
PMA monitor is used for monitoring of traffic. There is only easy monitor which write whole transaction to analysis port.

PMA driver
----------
PMA driver is used for driving PMA transactions to interface.
