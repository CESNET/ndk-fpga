.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Daniel Kondys <kondys@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _mfb_merger_simple_gen:

MFB Merger Simple
-----------------

.. vhdl:autoentity:: MFB_MERGER_SIMPLE

Using MASKING_EN parameter
^^^^^^^^^^^^^^^^^^^^^^^^^^

*True*: Allows switching of ports when reaching EOF in any of the regions regardless if higher
regions within a bus word contain other packets. Therefore, buswords where multiple packets occupy
multiple regions can get split.

*False*: A port switch can happen when reaching an EOF but only if there are no new packets
beginning in that bus word.

For example, in some configurations (like PCIe IPs), a first packet in a bus word can begin only on
byte 0. When masking would be set to true, after a port switch, some packets can begin on higher
bytes other than 0 in a bus word which would break a protocol.

MFB Merger Simple GEN
---------------------

.. vhdl:autoentity:: MFB_MERGER_SIMPLE_GEN
