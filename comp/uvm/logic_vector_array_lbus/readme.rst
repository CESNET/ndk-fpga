.. readme.rst: Documentation of the LOGIC VECTOR ARRAY LBUS environment
.. Copyright (C) 2024 CESNET z. s. p. o.
.. Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

.. SPDX-License-Identifier: BSD-3-Clause

***********************************
LOGIC VECTOR ARRAY LBUS Environment
***********************************

This environment has two high-level agents. The first one is a logic vector array agent that works with packet data. The second one is a logic vector agent that works with error data.
This package contains two environments. TX environment generates packet and error data and sends them to the DUT. RX environment generates the RDY signal and observes the RX interface.

Sequencers
==========

TX direction
------------

- **packet** is a logic vector array sequencer that handles packet data.
- **error** is a logic vector sequencer that handles error data.

Both sequencers pull the data from sequences together.

RX direction
------------

There is one sequencer of type *lbus::sequencer* that generates the RDY signal.

Both directions have two *analysis exports*. One export is for the logic vector array transactions, and the second is for the logic vector transactions.

Sequences
=========

- *sequence_tx* is a basic converting sequence.
- *sequence_tx_stop* is a sequence that generates only empty transactions.
- *sequence_tx_bursting* is a converting sequence with 'bursting' behavior.
