--!
--! \file  dp_bmem_V7_func.vhd
--! \brief Dual port BRAM for Virtex 7 functions
--! \author Pavel Benáček <benacek@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;

Package DP_BMEM_V7_PKG is

   -- -------------------------------------------
   -- Function prototypes
   -- -------------------------------------------
   --Next three functions are returning values wich could be found
   --in Xilinx 7 series libraries guide for HDL designs; sectionb
   --about BRAM_TDP_MACRO

   --Returns portion of data per BRAM
   function GET_BMEM_DATA_WIDTH_PORTION(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer;

   --Returns BRAM address width with respect to selected BRAM type and data width
   function GET_BMEM_ADDR_WIDTH(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer;

   --Returns BRAM write enable width with respect to selected BRAM type and data width
   function GET_BMEM_WE_WIDTH(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer;

   --Returns number of BRAMs which are needed for keeping of one word with
   --respect to selected BRAM type and DATA width
   function GET_BMEM_ON_WORD(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer;

   --Returns a number of BRAM rows
   function GET_BMEM_ROW_COUNT(BRAM_TYPE:integer;DATA_WIDTH:integer;ADDRESS_WIDTH:integer) return integer;

end  DP_BMEM_V7_PKG;

-- ----------------------------------------------------------------------------
--                      Package body declaration
-- ----------------------------------------------------------------------------

Package body DP_BMEM_V7_PKG is
   --Returns portion of data per BRAM
   function GET_BMEM_DATA_WIDTH_PORTION(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer is
   begin
      if(DATA_WIDTH > 0 and DATA_WIDTH <= 36)then
         --BRAM could use BRAM width as configured
         return DATA_WIDTH;
      else
         --Next decision depends on selected BRAM type. Use maximal
         --possible configuration with respect to actual. BRAM type match
         --maximal possible used data width
         return BRAM_TYPE;
      end if;
   end GET_BMEM_DATA_WIDTH_PORTION;

   --Returns BRAM depth with respect to selected BRAM type and data width
   function GET_BMEM_ADDR_WIDTH(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer is
   begin

      --Return the BRAM address width with respect
      --to data width variable
      if(DATA_WIDTH = 1)then
         if(BRAM_TYPE = 18)then
            return 14;
         else
            return 15;
         end if;

      elsif(DATA_WIDTH = 2)then
         if(BRAM_TYPE = 18)then
            return 13;
         else
            return 14;
         end if;

      elsif(DATA_WIDTH >=3 and DATA_WIDTH <= 4)then
         if(BRAM_TYPE = 18)then
            return 12;
         else
            return 13;
         end if;

      elsif(DATA_WIDTH >= 5 and DATA_WIDTH <= 9)then
         if(BRAM_TYPE = 18)then
            return 11;
         else
            return 12;
         end if;

      elsif(DATA_WIDTH >= 10 and DATA_WIDTH <= 18)then
         if(BRAM_TYPE = 18)then
            return 10;
         else
            return 11;
         end if;
      else
         --We need to use more BRAMs for one word.
         --Return BRAM address bus width of maximal
         --possible data width with respect to selected BRAM type
         if(BRAM_TYPE = 18)then
            return 11;
         else
            return 10;
         end if;
      end if;
   end GET_BMEM_ADDR_WIDTH;

   --Returns BRAM depth with respect to selected BRAM type and data width
   function GET_BMEM_WE_WIDTH(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer is
   begin

      --Return the BRAM WE width with respect to DATA width and BRAM type
      if(DATA_WIDTH > 0 and DATA_WIDTH <= 9)then
         return 1;
      elsif(DATA_WIDTH >= 10 and DATA_WIDTH <= 18)then
         return 2;
      else
         return 4;
      end if;

   end GET_BMEM_WE_WIDTH;

   --Returns number of BRAMs which are needed for keeping of one word with
   --respect to selected BRAM type and DATA width
   function GET_BMEM_ON_WORD(BRAM_TYPE:integer;DATA_WIDTH:integer) return integer is
      variable intCount    : integer;
      variable rest        : integer;
   begin
      --Normalize the data width to ONE BRAM (modulo operation)
      if(BRAM_TYPE = 18)then
         --Maximal BRAM width is 18
         rest := DATA_WIDTH mod 18;
      else
         --Maximal BRAM width is 36
         rest := DATA_WIDTH mod 36;
      end if;

      --Get a number of BRAMs, which will be totaly used
      if(BRAM_TYPE = 18)then
         intCount := DATA_WIDTH/18;
      else
         intCount := DATA_WIDTH/36;
      end if;

      --Return the corrected number of used brams
      if(rest = 0)then
         --We are effectivly using all BRAMs
         return intCount;
      else
         --We have to correct a used number of BRAMS. We need one more BRAM
         --because rest is not null
         return intCount+1;
      end if;
   end GET_BMEM_ON_WORD;

   --Returns a number of BRAM rows
   function GET_BMEM_ROW_COUNT(BRAM_TYPE:integer;DATA_WIDTH:integer;ADDRESS_WIDTH:integer) return integer is
      variable bmem_addr_width : integer;
   begin
      --Get the BRAM data width (all BRAMs will have this address width)
      bmem_addr_width := GET_BMEM_ADDR_WIDTH(BRAM_TYPE,DATA_WIDTH);

      --Return the rest of generic address widht and consumed BRAM address width
      if(ADDRESS_WIDTH > bmem_addr_width)then
         --We need more than one row
         return 2**(ADDRESS_WIDTH-bmem_addr_width);
      else
         --We need only one row
         return 1;
      end if;
   end GET_BMEM_ROW_COUNT;

end DP_BMEM_V7_PKG;
