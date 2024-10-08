/*
 * ethernet_II.sv: Ethernet II protocol
 * Copyright (C) 2008 CESNET
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
 * This class implements Ethernet II protocol. Class inherates from Layer
 * abstract class.
 */
class Ethernet_II extends Layer;
   /*
    * Randomizations constraints:
    * minSrcMAC - minimal source MAC address for randomization
    * maxSrcMAC - maximal source MAC address for randomization
    * minDstMAC - minimal destination MAC address for randomization
    * maxDstMAC - maximal destination MAC address for randomization
    *
    * Class atributes affected by randomization:
    * destinationMAC - destination MAC address
    * sourceMAC      - source MAC address
    * CRC            - CRC, random generated, not used due CRC striping
    *                  performed by IBUF
    *                  TODO: generate from packet data
    *
    * Class atributes not affected by randomization:
    * eType  - upper layer type, determinated by calling post_randomize method
    * useCRC - indicates if CRC is added as frame footer. Usualy CRC isn't
    *          added because it is striped by IBUF. 1 indicate that CRC is
    *          added and 0 indicate that CRC isn't added.
    *
    * Class constants:
    * headerSize - size of protocol header
    * footerSize - size of protocol footer
    */
         bit   [47:0]   minSrcMAC;
         bit   [47:0]   maxSrcMAC;
         bit   [47:0]   minDstMAC;
         bit   [47:0]   maxDstMAC;
   rand  bit   [47:0]   destinationMAC;
   rand  bit   [47:0]   sourceMAC;
         bit   [15:0]   eType;
   rand  bit   [32:0]   CRC;
         bit            useCRC;

   const int            headerSize = 14;
   const int            footerSize = 4;

   /*
    * Class constructor.
    */
   function new();
      typ = "ETHERNET";
      subtype = "II";
      name = "Ethernet II";
      level = 0;
      next = null;
      previous = null;
      errorProbability = 0;
      minSrcMAC = '0;
      maxSrcMAC = '1;
      minDstMAC = '0;
      maxDstMAC = '1;
      useCRC    = '0;
   endfunction: new

   /*
    * Constraint for randomization. Sets value ranges for random variables.
    */
   constraint c
   {
      destinationMAC inside {[minDstMAC:maxDstMAC]};
      sourceMAC inside {[minSrcMAC:maxSrcMAC]};
   }

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
   endfunction: post_randomize

   /*
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
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

      vystup[12] = eType[15:8];
      vystup[13] = eType[7:0];

      return vystup;
   endfunction: getHeader

   /*
    * Returns array of bytes, which contains protocol footer.
    */
   function data getFooter();
      data vystup = new[footerSize];

      vystup[0] =   CRC[31:24];
      vystup[1] =   CRC[23:16];
      vystup[2] =   CRC[15:8];
      vystup[3] =   CRC[7:0];

      return vystup;
   endfunction: getFooter

   /*
    * Returns class atribute by it's name in form of array of bytes.
    * Not implemented yet.
    */
   function data getAttributeByName(string name);
      data vystup;
      return vystup;
   endfunction: getAttributeByName

   /*
    * Returns array of bytes containing protocol and upper layers
    * protocol data.
    */
   function data getData();
      data header, payload, footer, vystup;

      header = getHeader();
      payload = next.getData();
      footer = getFooter();
      vystup = new [header.size() + payload.size() + ((useCRC == 1) ? footer.size() : 0)];

      foreach (header[j])
         vystup[j] = header[j];

      foreach (payload[j])
         vystup[header.size() + j] = payload[j];

      if (useCRC == 1)
         foreach (footer[j])
            vystup[header.size()+payload.size() + j] = footer[j];

      return vystup;
   endfunction: getData

   /*
    * Copy function.
    */
   function Layer copy();
      Ethernet_II protocol;
      protocol = new();
      protocol.destinationMAC = destinationMAC;
      protocol.sourceMAC = sourceMAC;
      protocol.eType = eType;
      protocol.CRC = CRC;

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
     * Check if upper layer protocol is compatibile with Ethernet II protocol.
     * This function is used by generator.
     *
     * Parameters:
     * typ     - type of protocol
     * subtype - subtype of protocol
     * name    - name of protocol (for special cases, mostly unused)
     *
     * Supported protocols:
     * IPv4, IPv6, MPLS
     */
   function bit checkType(string typ, string subtype ,string name);
      if (typ == "IP")
      begin
         if (subtype == "4")
            return 1'b1;
         if (subtype == "6")
            return 1'b1;
      end;

      if (typ == "MPLS")
         return 1'b1;

      /* if (typ == "ARP")
         return 1'b1;

      if (typ == "RARP")
         return 1'b1; */

      return 1'b0;
   endfunction: checkType

   /*
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("Ethernet II");
      $display("Destination MAC: 0x%x", destinationMAC);
      $display("Source MAC: 0x%x", sourceMAC);
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

endclass: Ethernet_II
