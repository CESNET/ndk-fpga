/*
 * ethernet_type_pkg.sv: SystemVerilog Ethernet type package
 * Copyright (C) 2009 CESNET
 * Author(s):  Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 * TODO:
 */

/*
 * This package contains values for Ethernet type field.
 */
package ethernet_type_pkg;
   const bit   [15:0]   IPV4 = 16'h0800;
   const bit   [15:0]   IPV6 = 16'h86DD;
   const bit   [15:0]   MPLSUNI = 16'h8847;
   const bit   [15:0]   MPLSMULTI = 16'h8848;
   const bit   [15:0]   ARP = 16'h0806;
   const bit   [15:0]   RARP = 16'h8035;
   const bit   [15:0]   VLANTAG = 16'h8100;
   const bit   [15:0]   VLANQ_in_QTAG1 = 16'h9100;
   const bit   [15:0]   VLANQ_in_QTAG2 = 16'h9200;
   const bit   [15:0]   VLANQ_in_QTAG3 = 16'h9300;
   const bit   [15:0]   VLANADTAG = 16'h88a8;
endpackage : ethernet_type_pkg
