/*
 * udp.sv: UDP protocol
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
 * This class implements UDP protocol. Class inherates from Layer
 * abstract class.
 */
class UDP extends Layer;
   /*
    * Randomizations constraints:
    * minSrcPort - minimal source UDP port for randomization
    * maxSrcPort - maximal source UDP port for randomization
    * minDstPort - minimal destination UDP port for randomization
    * maxDstPort - maximal destination UDP port for randomization
    *
    * Class atributes affected by randomization:
    * sourcePort           - source UDP port
    * destinationPort      - destination UDP port
    * checksum             - checksum of header and data, currently not
    *                        implemented
    *
    * Class atributes not affected by randomization:
    * length - length of combined header and payload in bytes, minimal size
    *          8 byte (header size)
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
         bit   [15:0]   length;
   rand  bit   [15:0]   checksum;

   const int            headerSize = 8;

   /*
    * Class constructor.
    */
   function new();
      typ = "UDP";
      subtype = "";
      name = "UDP";
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
    * Constraint for randomization. Sets value ranges for UDP ports.
    */
   constraint portsc
   {
      sourcePort inside {[1:65535]};
      destinationPort inside {[1:65535]};
      destinationPort inside {[minDstPort:maxDstPort]};
      sourcePort inside {[minSrcPort:maxSrcPort]};
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
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
      data vystup = new[headerSize];

      vystup[0] = sourcePort[15:8];
      vystup[1] = sourcePort[7:0];

      vystup[2] = destinationPort[15:8];
      vystup[3] = destinationPort[7:0];

      vystup[4] = length[15:8];
      vystup[5] = length[7:0];

      vystup[6] = checksum[15:8];
      vystup[7] = checksum[7:0];

      return vystup;
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
    * Not full implemented yet, only old IDS names (SRC for source UDP port
    * and DST for destination UDP port).
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
      UDP protocol;
      protocol = new();
      protocol.sourcePort = sourcePort;
      protocol.destinationPort = destinationPort;
      protocol.length = length;
      protocol.checksum = checksum;

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
    * Check if upper layer protocol is compatibile with UDP protocol.
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
      $display("UDP");
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
      begin
         length = next.getLength(0);
         return headerSize + next.getLength(split);
      end
      else
      begin
         length = headerSize;
         return headerSize;
      end
   endfunction: getLength

endclass: UDP
