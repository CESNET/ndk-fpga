.. readme.rst: Documentation of single component
.. Copyright (C) 2023 CESNET z. s. p. o.
.. Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _mvb_mux:


MVB MUX
-----------

Multi-value bus multiplexer. Selects, which input MVB will be transmitting to output MVB.

The selection is done base on received select transactions. For each RX transaction, there must be exactly one select transaction. If there is none, the component will wait until one is received.

.. vhdl:autoentity:: GEN_MVB_MUX
