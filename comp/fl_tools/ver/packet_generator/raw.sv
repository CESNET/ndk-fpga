/*
 * raw.sv: RAW layer
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
 * This class implements RAW protocol (unstructured data). Class inherates
 * from Layer abstract class.
 */
class RAW extends Layer;
   /*
    * Class atributes affected by randomization:
    * dataB - array of unstructured data.
    */
   rand byte unsigned dataB [];

   /*
    * Constraint for randomization. Sets size of data array and randomize
    * it's content.
    */
   constraint datas
   {
      dataB.size inside {[minMTU:maxMTU]};
   }

   /*
    * Class constructor.
    */
   function new();
      typ = "RAW";
      subtype = "";
      name = "RAW";
      level = 30;
      next = null;
      previous = null;
      errorProbability = 0;
   endfunction: new

   /*
    * Returns array of bytes, which contains unstructured data.
    */
   function data getHeader();
      return dataB;
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
    * No atribute to return.
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
      return getHeader();
   endfunction: getData

   /*
    * Copy function.
    */
   function Layer copy();
      RAW protocol;
      protocol = new();
      protocol.dataB = dataB;

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
    * Check if upper layer protocol is compatibile with RAW protocol.
    * This function is used by generator.
    *
    * Parameters:
    * typ     - type of protocol
    * subtype - subtype of protocol
    * name    - name of protocol (for special cases, mostly unused)
    *
    * Supported protocols:
    * NONE - no protocol upper than unstructured data.
    */
   function bit checkType(string typ, string subtype ,string name);
      return 1'b0;
   endfunction: checkType

   /*
    * Displays informations about protocol including upper layer protocols.
    */
   function void display();
      $display("RAW");
      $display("Length: %d", dataB.size);
      $display("MinMTU: %d", minMTU);
      $display("MaxMTU: %d", maxMTU);
      $display("-----------------------\n\n");
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
      if (split == 0)
         return dataB.size();
      else
         return 0;
   endfunction: getLength

endclass: RAW
