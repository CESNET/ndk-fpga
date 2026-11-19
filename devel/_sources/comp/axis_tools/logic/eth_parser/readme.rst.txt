.. Copyright (C) 2026 CESNET z. s. p. o.
.. Author(s): Jakub Cabal <cabal@cesnet.cz>
.. SPDX-License-Identifier: BSD-3-Clause

.. _axis_eth_parser:

AXI-Stream Ethernet Parser
==========================

.. vhdl:autoentity:: AXIS_ETH_PARSER_GEN

.. vhdl:autoentity:: AXIS_ETH_PARSER

Protocols
---------

The package ``axis_eth_parser_types`` defines one ``PROTO_*`` constant for each protocol.
The table describes what a stage of each protocol reads and how it selects the next protocol.
The header offset is the position of the first header byte in the frame.

.. list-table::
   :header-rows: 1

   * - Protocol
     - Bytes read
     - Header length in bytes
     - Next protocol
   * - ``PROTO_ETH``
     - 14
     - 14
     - Ethertype in bytes 12 and 13: 0x8100, 0x88A8 and 0x9100 select ``PROTO_VLAN``,
       0x8847 and 0x8848 select ``PROTO_MPLS``, 0x0800 selects ``PROTO_IPV4``,
       0x86DD selects ``PROTO_IPV6``.
   * - ``PROTO_VLAN``
     - 4
     - 4
     - Ethertype in bytes 2 and 3, with the same values as ``PROTO_ETH``.
   * - ``PROTO_MPLS``
     - 5
     - 4
     - ``PROTO_MPLS`` when the bottom of stack flag is 0.
       Otherwise bits 7:4 of byte 4 select the protocol: 4 selects ``PROTO_IPV4``, 6 selects ``PROTO_IPV6``.
   * - ``PROTO_IPV4``
     - 20
     - IHL × 4, or 20 when IHL is less than 5
     - Protocol field: 6 selects ``PROTO_TCP``, 17 selects ``PROTO_UDP``.
   * - ``PROTO_IPV6``
     - 40
     - 40
     - Next header field: 6 selects ``PROTO_TCP``, 17 selects ``PROTO_UDP``,
       0, 43, 44 and 60 select ``PROTO_IPV6EXT``.
   * - ``PROTO_IPV6EXT``
     - 8
     - (hdr_ext_len + 1) × 8
     - Next header field, with the same values as ``PROTO_IPV6``.
   * - ``PROTO_TCP``
     - 20
     - 20
     - None
   * - ``PROTO_UDP``
     - 8
     - 8
     - None

Any other value of the field ends the protocol chain.
The stages after the end of the chain report their header as not found.

Limitations
-----------

- The parser outputs only the bytes that the table lists. IPv4 options, TCP options and the
  data of IPv6 extension headers after byte 7 are not available.
- A header is reported as not found when the frame ends before all bytes that the stage reads.
  The output does not show whether such a header is missing or cut.
  Bytes of the header after these bytes can be missing from the frame.
- ``HDR_VLD`` is set only after the frame passes ``TX_AXI_TREADY``.
  The TX side must not hold ``TX_AXI_TREADY`` low until ``HDR_VLD`` is set.
- When a frame contains more headers of one protocol than ``PROTOCOLS`` has stages,
  the protocol chain ends after the last stage of this protocol.
- In an IPv4 or IPv6 fragment with a fragment offset other than 0, the frame contains no TCP or UDP header.
  The TCP and UDP stages then read data bytes of the fragment.
  Check ``fragment_offset`` of IPv4, or the IPv6 Fragment header (next header 44).
- The MPLS label stack does not announce the protocol after the last label.
  The ``PROTO_MPLS`` stage reads the IP version field of the next header for this purpose.
- A next header that would start after ``PKT_MTU`` ends the protocol chain.

Register stages
---------------

A register stage after a parser stage delays the AXI data and the protocol chain by one clock cycle.
It shortens the critical path from the header of one stage to the header extraction of the next stage.

- With ``STAGE_REG_AUTO = true``, ``get_stage_reg_auto(PROTOCOLS)`` selects the register stages.
  It places them after each ``PROTO_IPV4`` and ``PROTO_IPV6EXT`` stage, except after the last stage.
  These stages compute a variable header length, which makes the path longer.
- With ``STAGE_REG_AUTO = false``, bit i of ``STAGE_REG`` adds a register stage after stage i.

Each register stage adds one clock cycle of latency and registers for one AXI word.

Example
-------

The example parses VLAN tagged IPv6 frames and decodes the IPv6 header.

.. code-block:: vhdl

    constant PROTOCOLS : proto_array_t := (PROTO_ETH, PROTO_VLAN, PROTO_IPV6, PROTO_TCP, PROTO_UDP);
    constant IPV6_I    : natural       := get_stage_index(PROTOCOLS, PROTO_IPV6);
    ...
    ipv6_hdr   <= decode_ipv6(hdr_data(IPV6_I));
    ipv6_found <= hdr_found(IPV6_I);
