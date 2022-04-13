.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Byte array to pma convert enviroment
.. _uvm_byte_array_pma:

************************************
Byte array to pma convert enviroment
************************************

This enviroment serves for preparation of agents (configuration set and creation), their connection to right analysis export and starting sequence on the right sequencer. This environment connect Byte Array agent with PMA agent in fact.

Byte Array to PMA monitor
^^^^^^^^^^^^^^^^^^^^^^^^^
Function of this monitor is take PMA transaction descramble it, then choose if it is start, middle or end of high level transaction that depends on type of frame (``IDLE``, ``START``, ...). When the end of transaction occured, high level transaction is writed to analysis port. To accumulation of data is used easy fifo.

Byte Array to PMA Sequence
^^^^^^^^^^^^^^^^^^^^^^^^^^
This sequence is used for generation of encoded data in right way and then send it to driver. Ther is state machine, which generate data in the right way. First random amount of idles is generated, after this state is changed to start and start sequence is generated, after second chunk of start sequence is generated, then state is changed to data and after that data from high level sequence are cutted to chunks which has same width as PMA transaction and there are sended to driver. After all data are sended, then terminate sequence is generate, this sequence depends on amount of valid bytes of last two words in high level sequence. To every sequence is generated header which has only valid values and tehre is also generated header valid once per two clocks cycles. There is one constraint in randomization which set percentage of occurrence of the block lock in verification. Every PMA sequence which is generated is scramble by scrambler with polynom ``1 + x^39 + x^58``. 
