/*
 * icmp.sv: ICMP for IP protocol version 4
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
 * This class implements ICMP subprotocol of IPv4 protocol. Class inherates
 * from Layer abstract class.
 */
class ICMP extends Layer;
   /*
    * Class atributes affected by randomization:
    * iType     - ICMP type
    * code      - further specification of ICMP type
    * checksum  - checksum of ICMP, not implemented yet
    * id        - id value, mostly used with ECHO REPLAY ICMP message
    * iSequence - sequence value, mostly used with ECHO REPLAY ICMP message
    *
    * Class constants:
    * headerSize - size of protocol header
    */
   rand  bit   [7:0]    iType;
   rand  bit   [7:0]    code;
   rand  bit   [15:0]   checksum;
   rand  bit   [15:0]   id;
   rand  bit   [15:0]   iSequence;

   const int            headerSize = 8;

   /*
    * Class constructor.
    */
   function new();
      typ = "ICMP";
      subtype = "4";
      name = "ICMPv4";
      level = 20;
      next = null;
      previous = null;
      errorProbability = 0;
   endfunction: new

   /*
    * Constraint for randomization. Sets value for type field. For further
    * information about this types see list of IANA ICMP TYPE NUMBERS.
    */
   constraint iTypec
   {
      iType inside {0, [3:6], [8:18], [30:41]};
   }

   /*
    * Constraint for randomization. Sets value for code field according type
    * field. For further information about this codes see list of IANA ICMP
    * TYPE NUMBERS.
    */
   constraint codes
   {
      if (iType == 3)
         code inside {[0:13]};
      else if (iType == 5)
         code inside {[0:3]};
      else if (iType == 9)
         code inside {0, 16};
      else if (iType == 11)
         code inside {[0:1]};
      else if (iType == 12)
         code inside {[0:2]};
      else if (iType == 40)
         code inside {[0:5]};
      else
         code == 0;
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
   endfunction: post_randomize

   /*
    * Returns array of bytes, which contains protocol header.
    */
   function data getHeader();
      data vystup = new[headerSize];

      vystup[0] = iType;

      vystup[1] = code;

      vystup[2] = checksum[15:8];
      vystup[3] = checksum[7:0];

      vystup[4] = id[15:8];
      vystup[5] = id[7:0];

      vystup[6] = iSequence[15:8];
      vystup[7] = iSequence[7:0];

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
      ICMP protocol;
      protocol = new();
      protocol.iType = iType;
      protocol.code = code;
      protocol.checksum = checksum;
      protocol.id = id;
      protocol. iSequence =  iSequence;

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
    * Check if upper layer protocol is compatibile with ICMP subprotocol.
    * This function is used by generator.
    *
    * Parameters:
    * typ     - type of protocol
    * subtype - subtype of protocol
    * name    - name of protocol (for special cases, mostly unused)
    *
    * Supported protocols:
    * RAW
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
      $display("ICMPv4 \n");
      $display("Type: %d \n", iType);
      $display("Code: %d \n", code);
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
         return headerSize + next.getLength(split);
      else
         return headerSize;
   endfunction: getLength

endclass: ICMP
