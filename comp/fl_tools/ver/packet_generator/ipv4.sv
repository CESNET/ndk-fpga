/*
 * ipv4.sv: IP protocol version 4
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

import ip_protocol_pkg::*;

/*
 * This class implements IPv4 protocol. Class inherates from Layer
 * abstract class.
 */
class IPv4 extends Layer;
   /*
    * Randomizations constraints:
    * minSrcIP - minimal source IP address for randomization
    * maxSrcIP - maximal source IP address for randomization
    * minDstIP - minimal destination IP address for randomization
    * maxDstIP - maximal destination IP address for randomization
    *
    * Class atributes affected by randomization:
    * version            - version of IP, allways 4 for IPv4
    * headerLength       - number of 32-bit word in IP header (usualy 5, can be
    *                      up to 15 when options are used)
    * typeOfService      - type of service
    * identification     - used for identifying fragments of original IP packet
    * flags              - used for control/identyfying fragments
    * fragmentOffset     - offset of fragment to the begin of the original IP
    *                      packet, measured in 64-bit blocks
    * timeToLive         - datagram lifetime, measured in number of hops
    * headerChecksum     - checksum of the header, not implemented yet
    * sourceAddress      - source IP address
    * destinationAddress - destination IP address
    *
    * Class atributes not affected by randomization:
    * totalLength - packet size (header + upper layers data), computed
    *               after randomization
    * protocol    - upper layer protocol type, set according upper
    *               layer protocol
    * enableMultipleProtocolNesting - if true, other IP layers or ETHERNET can
    *                                 be nested in this IPv6 layer
    *
    * Class constants:
    * headerSize - size of protocol header
    */
         bit   [31:0]   minSrcIP;
         bit   [31:0]   maxSrcIP;
         bit   [31:0]   minDstIP;
         bit   [31:0]   maxDstIP;
   rand  bit   [3:0]    version;
   rand  bit   [3:0]    headerLength;
   rand  bit   [7:0]    typeOfService;
         bit   [15:0]   totalLength;
   rand  bit   [15:0]   identification;
   rand  bit   [2:0]    flags;
   rand  bit   [12:0]   fragmentOffset;
   rand  bit   [7:0]    timeToLive;
         bit   [7:0]    protocol;
   rand  bit   [15:0]   headerChecksum;
   rand  bit   [31:0]   sourceAddress;
   rand  bit   [31:0]   destinationAddress;

   const int            headerSize = 20;

         bit            enableMultipleProtocolNesting;

   /*
    * Class constructor.
    */
   function new();
      typ = "IP";
      subtype = "4";
      name = "IPv4";
      level = 10;
      next = null;
      previous = null;
      errorProbability = 0;
      minSrcIP = '0;
      maxSrcIP = '1;
      minDstIP = '0;
      maxDstIP = '1;
      enableMultipleProtocolNesting = 0;
   endfunction: new

   /*
    * Constraint for randomization. Sets value ranges for IP addresses.
    */
   constraint c
   {
      sourceAddress inside {[minDstIP:maxDstIP]};
      destinationAddress inside {[minSrcIP:maxSrcIP]};
   }

   /*
    * Constraint for randomization. Sets value ranges for version field.
    */
   constraint versionc
   {
      version == 4;
   }

   /*
    * Constraint for randomization. Sets value ranges for header length.
    * Allways 5, because options aren't supported yet.
    */
   constraint headerLengthc
   {
      headerLength == 5;
   }

   /*
    * Constraint for randomization. Sets value ranges for type of service field.
    */
   constraint typeOfServicec
   {
      typeOfService[7:6] == 0;
   }

   /*
    * Constraint for randomization. Sets value ranges for flags field.
    */
   constraint flagsc
   {
      /* flags[2] == 0;
      if (flags[1] == 1)
         flags[0] == 0;*/
      flags == '0;
   }

   /*
    * Post randomization sets upper layer type to protocol field. Value is
    * assigned according upper layer protocol type. It also set data length
    * boundaries for upper layer protocol.
    *
    * Supported upper layer protocols:
    * IPv4, IPv6, ICMP, TCP, UDP, ETHERNET, RAW
    */
   function void post_randomize();
      if (this.next.typ == "IP")
      begin
         if (this.next.subtype == "4")
            protocol = PROTO_IPV4;
         if (this.next.subtype == "6")
            protocol = PROTO_IPV6;
      end;

      if (this.next.typ == "ICMP")
         protocol = PROTO_ICMP;

      if (this.next.typ == "TCP")
         protocol = PROTO_TCP;

      if (this.next.typ == "UDP" )
         protocol = PROTO_UDP;

      if (this.next.typ == "ETHERNET" )
         protocol = PROTO_ETHERNET;

      if (this.next.typ == "RAW" )
         protocol = PROTO_RAW;

      if (next != null)
      begin
         next.minMTU = (minMTU - headerSize > 0) ? minMTU - headerSize : 0;
         next.maxMTU = (maxMTU - headerSize > 0) ? maxMTU - headerSize : 0;
         void'(next.randomize);
      end

   endfunction:  post_randomize

   /*
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
      data vystup = new[headerSize];
      bit [7:0] helper;

      helper[7:4] = version;
      helper[3:0] = headerLength;
      vystup[0] = helper;

      vystup[1] = typeOfService;

      vystup[2] = totalLength[15:8];
      vystup[3] = totalLength[7:0];

      vystup[4] = identification[15:8];
      vystup[5] = identification[7:0];

      helper[7:5] = flags;
      helper[4:0] = fragmentOffset[12:8];
      vystup[6] = helper;

      vystup[7] = fragmentOffset[7:0];

      vystup[8] = timeToLive;

      vystup[9] = protocol;

      vystup[10] = headerChecksum[15:8];
      vystup[11] = headerChecksum[7:0];

      vystup[12] = sourceAddress[31:24];
      vystup[13] = sourceAddress[23:16];
      vystup[14] = sourceAddress[15:8];
      vystup[15] = sourceAddress[7:0];

      vystup[16] = destinationAddress[31:24];
      vystup[17] = destinationAddress[23:16];
      vystup[18] = destinationAddress[15:8];
      vystup[19] = destinationAddress[7:0];

      return vystup;
   endfunction: getHeader

   /*
    * Returns array of bytes, which contains protocol footer.
    */
   function data getFooter();
      data vystup;
      return vystup;
   endfunction: getFooter

   /*
    * Returns class atribute by it's name in form of array of bytes.
    * Not full implemented yet, only old IDS names (SRC for source IP address
    * and DST for destination IP address).
    */
   function data getAttributeByName(string name);
      data vystup = new[4];
      if (name == "SRC")
      begin
         vystup[0] = sourceAddress[31:24];
         vystup[1] = sourceAddress[23:16];
         vystup[2] = sourceAddress[15:8];
         vystup[3] = sourceAddress[7:0];
      end

      if (name == "DST")
      begin
         vystup[0] = destinationAddress[31:24];
         vystup[1] = destinationAddress[23:16];
         vystup[2] = destinationAddress[15:8];
         vystup[3] = destinationAddress[7:0];
      end

      return vystup;
   endfunction: getAttributeByName

   /*
    * Returns array of bytes containing protocol and upper layers
    * protocol data.
    */
   function data getData();
      data header, payload, vystup;

      header = getHeader();
      payload = next.getData();

      vystup = new [header.size() + payload.size()];

      foreach (header[j])
         vystup[j] = header[j];

      foreach (payload[j])
         vystup[header.size() + j] = payload[j];

      return vystup;
   endfunction: getData

   /*
    * Copy function.
    */
   function Layer copy();
      IPv4 protocol;
      protocol = new();
      protocol.version = version;
      protocol.headerLength = headerLength;
      protocol.typeOfService = typeOfService;
      protocol.totalLength = totalLength;
      protocol.identification = identification;
      protocol.flags = flags;
      protocol.fragmentOffset = fragmentOffset;
      protocol.timeToLive = timeToLive;
      protocol.protocol = this.protocol;
      protocol.headerChecksum = headerChecksum;
      protocol.sourceAddress = sourceAddress;
      protocol.destinationAddress = destinationAddress;

      protocol.minSrcIP = minSrcIP;
      protocol.maxSrcIP = maxSrcIP;
      protocol.minDstIP = minDstIP;
      protocol.maxDstIP = maxDstIP;

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
    * Check if upper layer protocol is compatibile with IPv6 protocol.
    * This function is used by generator.
    *
    * Parameters:
    * typ     - type of protocol
    * subtype - subtype of protocol
    * name    - name of protocol (for special cases, mostly unused)
    *
    * Supported protocols:
    * IPv4, IPv6, ICMP, TCP, UDP, RAW, ETHERNET
    */
   function bit checkType(string typ, string subtype ,string name);
      if (enableMultipleProtocolNesting) begin
         if (typ == "IP")
         begin
            if (subtype == "4")
               return 1'b1;
            if (subtype == "6")
               return 1'b1;
         end;

         if (typ == "ETHERNET")
            return 1'b1;
      end

      if (typ == "ICMP")
         if (subtype == "4")
            return 1'b1;
         else
            return 1'b0;

      if (typ == "TCP")
         return 1'b1;

      if (typ == "UDP")
         return 1'b1;

      if (typ == "RAW")
         return 1'b1;

      return 1'b0;
   endfunction: checkType

   /*
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("IPv4");
      $display("Version: %d", version);
      $display("Type of service: 0x%x", typeOfService);
      $display("Source address: 0x%x", sourceAddress);
      $display("Destination address: 0x%x", destinationAddress);
      $display("TTL: %d", timeToLive);
      $display("Total length: 0x%x", totalLength);
      $display("Protocol: 0x%x", protocol);
      $display("Fragment offset: 0x%x", fragmentOffset);
      $display("Header checksum: 0x%x", headerChecksum);
      $display("-----------------------\n");
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
      begin
         totalLength = next.getLength(0) + headerSize;
         return headerSize + next.getLength(split);
      end
      else
      begin
         totalLength = headerSize;
         return headerSize;
      end
   endfunction: getLength

endclass: IPv4
