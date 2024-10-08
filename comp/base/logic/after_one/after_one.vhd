-- after_one.vhd: Generator vector with ones after one in input vector.
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

-- EXAMPLES:
-- DI = 00100000 ==>> DO = 11000000
-- DI = 00000100 ==>> DO = 11111000
-- DI = 00000000 ==>> DO = 00000000
-- DI = 00000001 ==>> DO = 11111110

entity AFTER_ONE is
   generic(
      DATA_WIDTH     : natural := 64;
      -- Type of implementation, allowed values are:
      --    "BEHAV" - Behavioral, better resources usage.
      --    "P-OR"  - Paraller OR, better timming.
      IMPLEMENTATION : string := "P-OR"
   );
   port(
      -- Input vector in one-hot encoding
      DI : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Output vector
      DO : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end AFTER_ONE;

architecture FULL of AFTER_ONE is

begin

   por_g : if IMPLEMENTATION = "P-OR" generate
      DO(0) <= '0';
      after_g : for i in 1 to DATA_WIDTH-1 generate
         DO(i) <= or DI(i-1 downto 0);
      end generate;
   end generate;

   behav_g : if IMPLEMENTATION = "BEHAV" generate
      behav_p : process(DI)
      begin
         DO <= (others => '0');
         temp_or : for i in 0 to DATA_WIDTH-2 loop
            if (DI(i) = '1') then
               DO(DATA_WIDTH-1 downto i+1) <= (others => '1');
               exit;
            end if;
         end loop;
      end process;
   end generate;

end architecture;
