/*
 * ethernet_II_dotad.sv: Ethernet II protocol with 802.1ad tag
 * Copyright (C) 2009 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

import ethernet_type_pkg::*;

/*
 * This class implements Ethernet II protocol with 802.1ad VLAN tagging.
 * Class inherates from Ethernet_II_dotq class.
 */
class Ethernet_II_dotad extends Ethernet_II_dotq;
   /*
    * Class constraints:
    * enable_old_Q_in_Q - enables old Q-in-Q (prior 802.1ad)
    *                   - TPID can be 0x8100, 0x9100, 0x9200 or 0x9300 instead
    *                     of 802.1ad 0x88a8
    *                   - Canonical Format Indicator is used instead of
    *                     Drop Eligible Indicator
    *
    * Class atributes affected by randomization:
    * serviceTPID - Tag Protocol Identifier
    * serviceTCI  - consists of:
    *               Priority [15:13]             - frame priority 0-7
    *               Drop Eligible Indicator [12] - when set true, frame can be
    *                                              discarded acording it's
    *                                              priority tag
    *               VLAN identifier [11:0]       - VLAN number
    *
    * Class constants:
    * headerSize - size of protocol header
    */

         bit   unsigned          enable_old_Q_in_Q;
   rand  bit   unsigned [15:0]   serviceTPID;
   rand  bit   unsigned [15:0]   serviceTCI;

   const int   unsigned          headerSize = 22;

   /*
    * Constraints for randomization. Sets value ranges for random variables.
    */
   constraint TCIc
   {
      TPID == VLANTAG;
      TCI[12] == 0;
      TCI[11:0] < 4095;
   }

   constraint serviceTCIc
   {
      if (enable_old_Q_in_Q == 1)
      {
         serviceTPID inside {VLANTAG, VLANQ_in_QTAG1, VLANQ_in_QTAG2, VLANQ_in_QTAG3};
         serviceTCI[12] == 0;
         serviceTCI[11:0] < 4095;
      }
      else
      {
         serviceTPID == VLANADTAG;
         serviceTCI[11:0] < 4095;
      }

   }

   /*
    * Class constructor.
    */
   function new();
      typ = "ETHERNET";
      subtype = "II 802.1ad";
      name = "Ethernet II 802.1ad";
      level = 0;
      next = null;
      previous = null;
      errorProbability = 0;
      useCRC = '0;
      enable_old_Q_in_Q = 0;
   endfunction: new

   /*
    * Post randomization sets upper layer type to eType field. Value is
    * assigned according upper layer protocol type. It also set data length
    * boundaries for upper layer protocol.
    *
    * Supported upper layer protocols:
    * IPv4, IPv6, MPLS
    */
   function void post_randomize();
      if (this.next.typ == "IP")
      begin
         if (this.next.subtype == "4")
            eType = IPV4;
         if (this.next.subtype == "6")
            eType = IPV6;
      end;

      if (this.next.typ == "MPLS")
         eType = MPLSUNI;

      /*if (this.next.typ == "ARP")
         eType = ARP;

      if (this.next.typ == "RARP")
         eType = RARP;*/

      // sets maximal and minimal length of next layer protocol data
      if (next != null)
      begin
        if (useCRC == 0)
         begin
            next.minMTU = (minMTU - headerSize > 0) ? minMTU - headerSize : 0;
            next.maxMTU = (maxMTU - headerSize > 0) ? maxMTU - headerSize : 0;
         end
         else
         begin
            next.minMTU = (minMTU - (headerSize + footerSize) > 0) ? minMTU - (headerSize + footerSize) : 0;
            next.maxMTU = (maxMTU - (headerSize + footerSize) > 0) ? maxMTU - (headerSize + footerSize) : 0;
         end;
         void'(next.randomize);
      end
   endfunction:  post_randomize

   /*
    * Returns array of bytes, which contains protocol header.
    */
   function  data getHeader();
      data vystup = new[headerSize];
      vystup[0]  = destinationMAC[47:40];
      vystup[1]  = destinationMAC[39:32];
      vystup[2]  = destinationMAC[31:24];
      vystup[3]  = destinationMAC[23:16];
      vystup[4]  = destinationMAC[15:8];
      vystup[5]  = destinationMAC[7:0];

      vystup[6]  = sourceMAC[47:40];
      vystup[7]  = sourceMAC[39:32];
      vystup[8]  = sourceMAC[31:24];
      vystup[9]  = sourceMAC[23:16];
      vystup[10] = sourceMAC[15:8];
      vystup[11] = sourceMAC[7:0];

      vystup[12] = serviceTPID[15:8];
      vystup[13] = serviceTPID[7:0];

      vystup[14] = serviceTCI[15:8];
      vystup[15] = serviceTCI[7:0];

      vystup[16] = TPID[15:8];
      vystup[17] = TPID[7:0];

      vystup[18] = TCI[15:8];
      vystup[19] = TCI[7:0];

      vystup[20] = eType[15:8];
      vystup[21] = eType[7:0];

      return vystup;
   endfunction: getHeader

   /*
    * Returns class atribute by it's name in form of array of bytes.
    * Not implemented yet.
    */
   function  data getAttributeByName(string name);
      data vystup;
      return vystup;
   endfunction: getAttributeByName

   /*
    * Copy function.
    */
   function Layer copy();
      Ethernet_II_dotad protocol;
      protocol = new();
      protocol.destinationMAC = destinationMAC;
      protocol.sourceMAC = sourceMAC;
      protocol.eType = eType;
      protocol.CRC = CRC;
      protocol.TCI = TCI;
      protocol.TPID = TPID;
      protocol.serviceTCI = serviceTCI;
      protocol.serviceTPID = serviceTPID;
      protocol.enable_old_Q_in_Q = enable_old_Q_in_Q;

      protocol.typ = typ;
      protocol.subtype = subtype;
      protocol.name = name;
      protocol.level = level;
      protocol.next = next;
      protocol.previous = previous;
      protocol.errorProbability = errorProbability;
      protocol.minMTU = minMTU;
      protocol.maxMTU = maxMTU;

      return protocol;
   endfunction: copy

   /*
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("Ethernet II 802.1ad");
      $display("Destination MAC: 0x%x", destinationMAC);
      $display("Source MAC: 0x%x", sourceMAC);
      $display("serviceTPID: 0x%x", serviceTPID);
      $display("serviceTCI: 0x%x", serviceTCI);
      $display("TPID: 0x%x", TPID);
      $display("TCI: 0x%x", TCI);
      $display("Type: 0x%x", eType);
      if (useCRC == 1)
         $display("CRC: 0x%x", CRC);
      $display("-----------------------\n\n");
      if (next != null)
         next.display();
   endfunction: display

   /*
    * Returns length of protocol data plus all upper level protocols data
    * length.
    *
    * Parameters:
    * split - if set length of RAW protocol layer isn't returned, otherwise
    *         the length of RAW protocol layer is returned.
    */
   function int getLength(bit split);
      if (next != null)
         return ((useCRC == 1) ? headerSize + footerSize : headerSize) + next.getLength(split);
      else
         return (useCRC == 1) ? headerSize + footerSize : headerSize;
   endfunction: getLength

endclass: Ethernet_II_dotad
