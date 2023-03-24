.. readme.rst: Documentation of single component
.. Copyright (C) 2023 CESNET z. s. p. o.
.. Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _mvb_demux:


MVB DEMUX
-----------

Multi-value bus item demultiplexer. For each item, there is a select signal, which determines to which TX port the item will be transmitted.

Transaction on RX MVB is executed, when all ports, to which at least one item will be transmitted, have DST_RDY asserted. Ports, which will not receive any item, do not have to have DST_RDY asserted.

.. vhdl:autoentity:: GEN_MVB_DEMUX
