-- extrem_select.vhd: Extrem selection unit architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_EXTREM_SELECT is
   generic(
      DATA_WIDTH     : integer;
      VECTOR_COUNT   : integer;
      MIN1_MAX0      : boolean
   );
   port(
      -- input vectors
      DI             : in  std_logic_vector((VECTOR_COUNT*DATA_WIDTH)-1
                                                                  downto 0);
      -- extrem bus ('1' -> this vector is the greatest/least)
      EXTREM         : out std_logic_vector(VECTOR_COUNT-1 downto 0)
   );
end entity FLB_EXTREM_SELECT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_EXTREM_SELECT is

   -- ------------------ Signals declaration ----------------------------------
   signal cmp_bus          : std_logic_vector(VECTOR_COUNT*VECTOR_COUNT-1
                                                                     downto 0);
   signal and_bus          : std_logic_vector(VECTOR_COUNT*VECTOR_COUNT-1
                                                                     downto 0);
begin

   -- generate necessary comparators ------------------------------------------
   GEN_MIN: if (MIN1_MAX0) generate
      GEN_CMP_BUS: for i in 0 to VECTOR_COUNT-1 generate
         GEN_COMPARATORS: for j in 0 to VECTOR_COUNT-1 generate

            GEN_COMPARATOR: if j /= i generate
               -- ------------------ Comparator ----------------------------------
               cmp_bus(i*VECTOR_COUNT+j) <= '1'
                  when (DI((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
                     <= DI((j+1)*DATA_WIDTH-1 downto j*DATA_WIDTH)) else '0';
            end generate;

            GEN_ONE: if j = i generate
               cmp_bus(i*VECTOR_COUNT+j) <= '1';
            end generate;

         end generate;
      end generate;
   end generate;

   GEN_MAX: if (not MIN1_MAX0) generate
      GEN_CMP_BUS: for i in 0 to VECTOR_COUNT-1 generate
         GEN_COMPARATORS: for j in 0 to VECTOR_COUNT-1 generate

            GEN_COMPARATOR: if j /= i generate
               -- ------------------ Comparator ----------------------------------
               cmp_bus(i*VECTOR_COUNT+j) <= '1'
                  when (DI((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
                     >= DI((j+1)*DATA_WIDTH-1 downto j*DATA_WIDTH)) else '0';
            end generate;

            GEN_ONE: if j = i generate
               cmp_bus(i*VECTOR_COUNT+j) <= '1';
            end generate;

         end generate;
      end generate;
   end generate;

   -- generate AND bus --------------------------------------------------------
   GEN_AND_BUS: for i in 0 to VECTOR_COUNT-1 generate
      GEN_ANDS: for j in 0 to VECTOR_COUNT-1 generate

         GEN_AND: if j /= 0 generate
            -- ------------------ AND -----------------------------------------
            and_bus(i*VECTOR_COUNT+j) <=
               and_bus(i*VECTOR_COUNT+j-1) and cmp_bus(i*VECTOR_COUNT+j);

         end generate;

         GEN_ONE: if j = 0 generate
            and_bus(i*VECTOR_COUNT+j) <= cmp_bus(i*VECTOR_COUNT+j);
         end generate;

      end generate;
   end generate;

   -- generate output ---------------------------------------------------------
   GEN_OUT: for i in 0 to VECTOR_COUNT-1 generate
      EXTREM(i) <= and_bus(i*VECTOR_COUNT+VECTOR_COUNT-1);
   end generate;

end architecture full;
