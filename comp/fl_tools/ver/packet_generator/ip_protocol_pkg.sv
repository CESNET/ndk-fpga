/*
 * ip_protocol_pkg.sv: SystemVerilog IP protocol package
 * Copyright (C) 2009 CESNET
 * Author(s):  Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

/*
 * This package contains values for IPv4/IPv6 protocol/next header field.
 * See IANA list of protocol numbers or RFC 791 for more.
 */
package ip_protocol_pkg;
   const bit   [7:0]   PROTO_IPV4 = 8'd4;
   const bit   [7:0]   PROTO_IPV6 = 8'd41;
   const bit   [7:0]   PROTO_ICMP = 8'd1;
   const bit   [7:0]   PROTO_ICMPv6 = 8'd58;
   const bit   [7:0]   PROTO_TCP = 8'd6;
   const bit   [7:0]   PROTO_UDP = 8'd17;
   const bit   [7:0]   PROTO_ETHERNET = 8'd97;
   const bit   [7:0]   PROTO_RAW = 8'hFF;
endpackage : ip_protocol_pkg
