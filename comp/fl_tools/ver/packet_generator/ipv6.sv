/*
 * ipv6.sv: IP protocol version 6
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
 * This class implements IPv6 protocol. Class inherates from Layer
 * abstract class.
 */
class IPv6 extends Layer;
   /*
    * Randomizations constraints:
    * minSrcIP - minimal source IP address for randomization
    * maxSrcIP - maximal source IP address for randomization
    * minDstIP - minimal destination IP address for randomization
    * maxDstIP - maximal destination IP address for randomization
    *
    * Class atributes affected by randomization:
    * version            - version of IP, allways 6 for IPv6
    * trafficClass       - priority of packet
    * flowLabel          - quality of service management, currently not used
    * hopLimit           - datagram lifetime, measured in number of hops
    * sourceAddress      - source IP address
    * destinationAddress - destination IP address
    *
    * Class atributes not affected by randomization:
    * payloadLength                 - length of payload data
    * nextHeader                    - upper layer protocol type, set according
    *                                 upper layer protocol. It is used also for
    *                                 IPv6 options
    * enableMultipleProtocolNesting - if true, other IP layers or ETHERNET can
    *                                 be nested in this IPv6 layer
    *
    * Class constants:
    * headerSize - size of protocol header
    */
         bit   [127:0]  minSrcIP;
         bit   [127:0]  maxSrcIP;
         bit   [127:0]  minDstIP;
         bit   [127:0]  maxDstIP;
   rand  bit   [3:0]    version;
   rand  bit   [7:0]    trafficClass;
   rand  bit   [19:0]   flowLabel;
         bit   [15:0]   payloadLength;
         bit   [7:0]    nextHeader;
   rand  bit   [7:0]    hopLimit;
   rand  bit   [127:0]  sourceAddress;
   rand  bit   [127:0]  destinationAddress;

   const int            headerSize = 40;

         bit            enableMultipleProtocolNesting;

   /*
    * Class constructor.
    */
   function new();
      typ = "IP";
      subtype = "6";
      name = "IPv6";
      level = 10;
      next = null;
      previous = null;
      errorProbability = 0;
      minSrcIP = '0;
      maxSrcIP = '1;
      minDstIP = '0;
      maxDstIP = '1;
      enableMultipleProtocolNesting = 1;
   endfunction: new

   /*
    * Constraint for randomization. Sets value ranges for version field.
    */
   constraint versionc
   {
      version == 6;
   }

   /*
    * Constraint for randomization. Sets value ranges for IP addresses.
    */
   constraint c
   {
      sourceAddress inside {[minDstIP:maxDstIP]};
      destinationAddress inside {[minSrcIP:maxSrcIP]};
   }

   /*
    * Post randomization sets upper layer type to nextHeader field. Value is
    * assigned according upper layer protocol type. It also set data length
    * boundaries for upper layer protocol.
    *
    * Supported upper layer protocols:
    * IPv4, IPv6, ICMPv6, TCP, UDP, ETHERNET, RAW
    */
   function void post_randomize();
      if (this.next.typ == "IP")
      begin
         if (this.next.subtype == "4")
            nextHeader = PROTO_IPV4;
         if (this.next.subtype == "6")
            nextHeader = PROTO_IPV6;
      end;

      if (this.next.typ == "ICMP")
         nextHeader = PROTO_ICMPv6;

      if (this.next.typ == "TCP")
         nextHeader = PROTO_TCP;

      if (this.next.typ == "UDP" )
         nextHeader = PROTO_UDP;

      if (this.next.typ == "ETHERNET" )
         nextHeader = PROTO_ETHERNET;

      if (this.next.typ == "RAW" )
         nextHeader = PROTO_RAW;

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
      data vystup=new[headerSize];
      bit [7:0] helper;

      helper[7:4] = version;
      helper[3:0] = trafficClass[7:4];
      vystup[0] = helper;

      helper[7:4] = trafficClass[3:0];
      helper[3:0] = flowLabel[19:16];
      vystup[1] = helper;

      vystup[2] = flowLabel[15:8];
      vystup[3] = flowLabel[7:0];

      vystup[4] = payloadLength[15:8];
      vystup[5] = payloadLength[7:0];

      vystup[6] = nextHeader;

      vystup[7] = hopLimit;

      vystup[8]  = sourceAddress[127:120];
      vystup[9]  = sourceAddress[119:112];
      vystup[10] = sourceAddress[111:104];
      vystup[11] = sourceAddress[103:96];
      vystup[12] = sourceAddress[95:88];
      vystup[13] = sourceAddress[87:80];
      vystup[14] = sourceAddress[79:72];
      vystup[15] = sourceAddress[71:64];
      vystup[16] = sourceAddress[63:56];
      vystup[17] = sourceAddress[55:48];
      vystup[18] = sourceAddress[47:40];
      vystup[19] = sourceAddress[39:32];
      vystup[20] = sourceAddress[31:24];
      vystup[21] = sourceAddress[23:16];
      vystup[22] = sourceAddress[15:8];
      vystup[23] = sourceAddress[7:0];

      vystup[24] = destinationAddress[127:120];
      vystup[25] = destinationAddress[119:112];
      vystup[26] = destinationAddress[111:104];
      vystup[27] = destinationAddress[103:96];
      vystup[28] = destinationAddress[95:88];
      vystup[29] = destinationAddress[87:80];
      vystup[30] = destinationAddress[79:72];
      vystup[31] = destinationAddress[71:64];
      vystup[32] = destinationAddress[63:56];
      vystup[33] = destinationAddress[55:48];
      vystup[34] = destinationAddress[47:40];
      vystup[35] = destinationAddress[39:32];
      vystup[36] = destinationAddress[31:24];
      vystup[37] = destinationAddress[23:16];
      vystup[38] = destinationAddress[15:8];
      vystup[39] = destinationAddress[7:0];

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
      data vystup = new[16];

      if (name == "SRC")
      begin
         vystup[0] = sourceAddress[127:120];
         vystup[1] = sourceAddress[119:112];
         vystup[2] = sourceAddress[111:104];
         vystup[3] = sourceAddress[103:96];
         vystup[4] = sourceAddress[95:88];
         vystup[5] = sourceAddress[87:80];
         vystup[6] = sourceAddress[79:72];
         vystup[7] = sourceAddress[71:64];
         vystup[8] = sourceAddress[63:56];
         vystup[9] = sourceAddress[55:48];
         vystup[10] = sourceAddress[47:40];
         vystup[11] = sourceAddress[39:32];
         vystup[12] = sourceAddress[31:24];
         vystup[13] = sourceAddress[23:16];
         vystup[14] = sourceAddress[15:8];
         vystup[15] = sourceAddress[7:0];
      end

      if (name == "DST")
      begin
         vystup[0] = destinationAddress[127:120];
         vystup[1] = destinationAddress[119:112];
         vystup[2] = destinationAddress[111:104];
         vystup[3] = destinationAddress[103:96];
         vystup[4] = destinationAddress[95:88];
         vystup[5] = destinationAddress[87:80];
         vystup[6] = destinationAddress[79:72];
         vystup[7] = destinationAddress[71:64];
         vystup[8] = destinationAddress[63:56];
         vystup[9] = destinationAddress[55:48];
         vystup[10] = destinationAddress[47:40];
         vystup[11] = destinationAddress[39:32];
         vystup[12] = destinationAddress[31:24];
         vystup[13] = destinationAddress[23:16];
         vystup[14] = destinationAddress[15:8];
         vystup[15] = destinationAddress[7:0];
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
      IPv6 protocol;
      protocol = new();
      protocol.version = version;
      protocol.trafficClass = trafficClass;
      protocol.flowLabel = flowLabel;
      protocol.payloadLength = payloadLength;
      protocol.nextHeader = nextHeader;
      protocol.hopLimit = hopLimit;
      protocol.sourceAddress = sourceAddress;
      protocol.destinationAddress = destinationAddress;

      protocol.minSrcIP = minSrcIP;
      protocol.maxSrcIP = maxSrcIP;
      protocol.minDstIP = minDstIP;
      protocol.maxDstIP = maxDstIP;

      protocol.enableMultipleProtocolNesting = enableMultipleProtocolNesting;

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
    * IPv4, IPv6, ICMPv6, TCP, UDP, RAW, ETHERNET
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

      if (typ == "ICMP") begin
         if (subtype == "6")
            return 1'b1;
         else
            return 1'b0;
      end

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
      $display("IPv6 \n");
      $display("Source address: 0x%x \n", sourceAddress);
      $display("Destination address: 0x%x \n", destinationAddress);
      $display("Hop Limit: %d \n", hopLimit);
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
      begin
         payloadLength = next.getLength(0);
         return headerSize + next.getLength(split);
      end
      else
      begin
         payloadLength = 0;
         $stop;
         return headerSize;
      end
   endfunction: getLength

endclass: IPv6
