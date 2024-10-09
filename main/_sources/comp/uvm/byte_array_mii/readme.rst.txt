.. readme.rst: Documentation of Byte array to MII transitional environment
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Oliver Gurka   <xgurka00@stud.fit.vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

******************************************
Byte array to MII transitional environment
******************************************

The purpose of this environment is to create MII and Byte array agents, set them up correctly, introduce randomness to data generation, and guarantee, that this data will be sent and read as standard defines. This environment allows to use multi-channel xMII bus and one cannot verify components that are using the MII bus, without this high-level environment.

Usage
^^^^^
There are two types of environment: RX and TX. To use the RX environment, instantiate it, and run byte_array sequence on the high-level agent (if active). To use the TX environment, just instantiate it, no need to run any sequences.

monitor.sv
^^^^^^^^^^
The monitor takes low-level xMII transactions and extracts data from them. It creates one byte_array transaction for a frame transmitted.

sequencer.sv
^^^^^^^^^^^^
This sequencer contains a reference to a high-level sequencer.

env.sv
^^^^^^
This file contains RX and TX environments. RX environment, if active, takes high-level transactions from the byte_array agent, transforms them to low-level xMII transactions and sends them to the interface. TX environment, if active, drives the CLK_EN signal.

sequence_rx_base.sv
^^^^^^^^^^^^^^^^^^^
This file contains a base class for all RX sequences. It is recommended for all RX sequences to inherit from them. They can be modified by creating specific instances of classes described below.

sequence_tx_base.sv
^^^^^^^^^^^^^^^^^^^
This file contains a base class for all TX sequences. It is recommended for all TX sequences to inherit from them. They can be modified by creating specific instances of classes described below.

ce_generator.sv
^^^^^^^^^^^^^^^
Classes in this file take care of generating clock enable signal.

wrapper.sv
^^^^^^^^^^
This class takes an array (FIFO, to make implementation easier) of bytes as input and adds the start of frame delimiter and preamble to the beginning of data, and appends the end of frame delimiter to the end. It also creates control logic array for the whole wrapped array of bytes

ipg_generator.sv
^^^^^^^^^^^^^^^^
This class appends a random number (between idle_count_min and idle_count_max) of idle octets to the wrapped frame and control array.

channel_align.sv
^^^^^^^^^^^^^^^^
This class appends as many idle octets to the array as needed to make sure, that the next frame starts on lane 0 of any channel. In other words, it fills the remaining free bytes of the current channel with idle octets.

data_buffer.sv
^^^^^^^^^^^^^^
This class accumulates data generated in pipeline (byte array -> wrapper -> ipg_generator -> channel_align -> data_buffer) until low-level transaction can be generated. In case, when more than one low-level transaction can be generated, it informs the user about it and one can retrieve data from it until no low-level transaction can be generated. In case no more high-level transactions will be generated, it can generate idle octets until one, last low-level transaction can be generated (flush).

As the last step, low-level transactions are distributed accordingly to channels.


sequence_rx.sv and sequence_tx.sv
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
These files contain sequences specific by different speeds (amount of idle octets) and clock enable patterns.
