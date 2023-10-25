.. readme.rst: Documentation of single component
.. Copyright (C) 2023 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Buffer verification 
.. _uvm_buffer:

************
BUFFER
************

Verification Plan
^^^^^^^^^^^^^^^^^

========   ================================================                                                                     ===========
ID          Description                                                                                                         Test
========   ================================================                                                                     ===========
1          Send 20000 packet withnout error flag. On output have to be at least 90% of them
2          Speed test. Send packet 100% - 90% input speed Pactek withnout error flag. Output speed cannot drop bellow 85%. Output DST_RDY have to be set allways to one
========   ================================================                                                                     ===========

