.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Byte arry to lii convert enviroment
.. _uvm_byte_array_mii:

************************************
Byte Array to LII convert enviroment
************************************
This enviroment serves for preparation of agents (configuration set and creation), their connection to right analysis export and starting sequence on the right sequencer. This enviroment connect Byte Array agent with LII agent in fact.

Byte Array to LII monitor
^^^^^^^^^^^^^^^^^^^^^^^^^
This monitor take LII specified number (it depends on the Length of Byte Array transaction) of transaction, merge them to one Byte Array transaction and writes it to analysis port. For acumulation of LII transactions is used fifo which only store all those transactions to his own memory.

Byte Array to LII Sequence
^^^^^^^^^^^^^^^^^^^^^^^^^^
This sequence has one quest and that is cutting of Byte array sequence to bytes and set ports of LII request to right values. SOF will be asserted when first chunk of transaction arrive and EOF will be asserted when the last chunk of transaction arrive. If it is last chunk of transaction then it set to BYTES_VLD number of valid bytes of that chunk. At the end is sequence send to driver. There is also task which send empty sequence when frame is null.
