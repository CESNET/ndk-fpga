/*
 * tcp.sv: TCP protocol
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

/*
 * This class implements TCP protocol. Class inherates from Layer
 * abstract class.
 */
class TCP extends Layer;
   /*
    * Randomizations constraints:
    * minSrcPort - minimal source TCP port for randomization
    * maxSrcPort - maximal source TCP port for randomization
    * minDstPort - minimal destination TCP port for randomization
    * maxDstPort - maximal destination TCP port for randomization
    *
    * Class atributes affected by randomization:
    * sourcePort           - source TCP port
    * destinationPort      - destination TCP port
    * sequenceNumber       - sequence number
    * acknowledgmentNumber - if ACK flag set, this field contains next expected
    *                         byte number
    * dataOffset           - size of TCP header (can be 5 - 15, currently 5
    *                        because Options aren't supported)
    * reserved             - reserved by specification
    * flags                - TCP flags (CWR, ECE, URG, ACK, PSH, RST, SYN
    *                        and FIN see specification for their meaning)
    * windowSize           - size of receive window, used for flow control
    * checksum             - checksum of header and data, currently not
    *                        implemented
    * urgentPointer        - sequence number of last urgent byte (used when
    *                        URG flag is set)
    *
    * Class constants:
    * headerSize - size of protocol header
    */
         bit   [15:0]   minSrcPort;
         bit   [15:0]   maxSrcPort;
         bit   [15:0]   minDstPort;
         bit   [15:0]   maxDstPort;
   rand  bit   [15:0]   sourcePort;
   rand  bit   [15:0]   destinationPort;
   rand  bit   [31:0]   sequenceNumber;
   rand  bit   [31:0]   acknowledgmentNumber;
   rand  bit   [3:0]    dataOffset;
   rand  bit   [3:0]    reserved;
   rand  bit   [7:0]    flags;
   rand  bit   [15:0]   windowSize;
   rand  bit   [15:0]   checksum;
   rand  bit   [15:0]   urgentPointer;

   const int            headerSize = 20;

   /*
    * Constraint for randomization. Sets value ranges for TCP ports.
    */
   constraint portsc
   {
      sourcePort inside {[1:65535]};
      destinationPort inside {[1:65535]};
      destinationPort inside {[minDstPort:maxDstPort]};
      sourcePort inside {[minSrcPort:maxSrcPort]};
   }

   /*
    * Constraint for randomization. Sets value ranges for data offset.
    * Currently only to 5.
    */
   constraint dataOffsetc
   {
      dataOffset == 5;
   }

   /*
    * Constraint for randomization. Sets value ranges for reserved field.
    */
   constraint reservedc
   {
      reserved == 0;
   }

   /*
    * Constraint for randomization. Sets value ranges for TCP flags.
    */
   constraint flagsc
   {
      if (flags[0] == 1)
         flags[7:1] == 0;
      else if (flags[1] == 1)
      {
         flags[6:5] == 0;
         flags[3:2] == 0;
      }
      else if (flags[2] == 1)
      {
         flags[7:3] == 0;
         flags[1:0] == 0;
      }
      else if (flags[4] == 1)
      {
         flags[7] == 0;
         flags[5] == 0;
         flags[3:2] == 0;
         flags[0] == 0;
      }
   }

   /*
    * Post randomization sets data length boundaries for upper layer protocol.
    */
   function void post_randomize();
      if (next != null)
      begin
         next.minMTU = (minMTU - headerSize > 0) ? minMTU - headerSize : 0;
         next.maxMTU = (maxMTU - headerSize > 0) ? maxMTU - headerSize : 0;
         void'(next.randomize);
      end
   endfunction:  post_randomize

   /*
    * Class constructor.
    */
   function new();
      typ = "TCP";
      subtype = "";
      name = "TCP";
      level = 20;
      next = null;
      previous = null;
      errorProbability = 0;
      minSrcPort = '0;
      maxSrcPort = '1;
      minDstPort = '0;
      maxDstPort = '1;
   endfunction: new

   /*
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
      data  vystup = new[headerSize];
      bit [7:0] helper;

      vystup[0] = sourcePort[15:8];
      vystup[1] = sourcePort[7:0];

      vystup[2] = destinationPort[15:8];
      vystup[3] = destinationPort[7:0];

      vystup[4] = sequenceNumber[31:24];
      vystup[5] = sequenceNumber[23:16];
      vystup[6] = sequenceNumber[15:8];
      vystup[7] = sequenceNumber[7:0];

      vystup[8] = acknowledgmentNumber[31:24];
      vystup[9] = acknowledgmentNumber[23:16];
      vystup[10] = acknowledgmentNumber[15:8];
      vystup[11] = acknowledgmentNumber[7:0];

      helper[7:4] = dataOffset;
      helper[3:0] = reserved;
      vystup[12] = helper;

      vystup[13] = flags;

      vystup[14] = windowSize[15:8];
      vystup[15] = windowSize[7:0];

      vystup[16] = checksum[15:8];
      vystup[17] = checksum[7:0];

      vystup[18] = urgentPointer[15:8];
      vystup[19] = urgentPointer[7:0];

      return  vystup;
   endfunction: getHeader

   /*
    * Returns array of bytes, which contains protocol footer.
    */
   function data getFooter();
      data  vystup;
      return  vystup;
   endfunction: getFooter

   /*
    * Returns class atribute by it's name in form of array of bytes.
    * Not full implemented yet, only old IDS names (SRC for source TCP port,
    * DST for destination TCP port and Flags for TCP flags).
    */
   function data getAttributeByName(string name);
      data  vystup = new[2];
      if (name == "SRC")
      begin
         vystup[0] = sourcePort[15:8];
         vystup[1] = sourcePort[7:0];
      end


      if (name == "DST")
      begin
         vystup[0] = destinationPort[15:8];
         vystup[1] = destinationPort[7:0];
      end

      if (name == "Flags")
      begin
         vystup[0][7:4] = dataOffset;
         vystup[0][3:0] = reserved;
         vystup[1] = flags;
      end

      return  vystup;
   endfunction: getAttributeByName

   /*
    * Returns array of bytes containing protocol and upper layers
    * protocol data.
    */
   function data getData();
      data header, payload,  vystup;

      header = getHeader();
      payload = next.getData();
      vystup = new [header.size() + payload.size()];

      foreach (header[j])
         vystup[j] = header[j];

      foreach (payload[j])
         vystup[header.size() + j] = payload[j];

      return  vystup;
   endfunction: getData

   /*
    * Copy function.
    */
   function Layer copy();
      TCP protocol;
      protocol = new();
      protocol.sourcePort = sourcePort;
      protocol.destinationPort = destinationPort;
      protocol.sequenceNumber = sequenceNumber;
      protocol.acknowledgmentNumber = acknowledgmentNumber;
      protocol.dataOffset = dataOffset;
      protocol.reserved = reserved;
      protocol.flags = flags;
      protocol.windowSize = windowSize;
      protocol.checksum = checksum;
      protocol.urgentPointer = urgentPointer;

      protocol.minSrcPort = minSrcPort;
      protocol.maxSrcPort = maxSrcPort;
      protocol.minDstPort = minDstPort;
      protocol.maxDstPort = maxDstPort;

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
    * Check if upper layer protocol is compatibile with TCP protocol.
    * This function is used by generator.
    *
    * Parameters:
    * typ     - type of protocol
    * subtype - subtype of protocol
    * name    - name of protocol (for special cases, mostly unused)
    *
    * Supported protocols:
    * RAW, RAWPattern
    */
   function bit checkType(string typ, string subtype ,string name);
      if (typ == "RAW")
         return 1'b1;

      return 1'b0;
   endfunction: checkType

   /*
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("TCP");
      $display("Source port: %d", sourcePort);
      $display("Destination port: %d", destinationPort);
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
         return headerSize + next.getLength(split);
      else
         return headerSize;
   endfunction: getLength

endclass: TCP
