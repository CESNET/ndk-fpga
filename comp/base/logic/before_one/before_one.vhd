-- after_one.vhd: Generator vector with ones before one in input vector.
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

-- EXAMPLES:
-- DI = 00100000 ==>> DO = 00011111
-- DI = 00000100 ==>> DO = 00000011
-- DI = 00000000 ==>> DO = 00000000
-- DI = 10000000 ==>> DO = 01111111

entity BEFORE_ONE is
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
end BEFORE_ONE;

architecture FULL of BEFORE_ONE is

   signal di_rot : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal do_rot : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

   --! rotate input vector, first bit is last bit, etc.
   di_rot_g : for i in 0 to DATA_WIDTH-1 generate
      di_rot(DATA_WIDTH-1-i) <= DI(i);
   end generate;

   after_one_i : entity work.AFTER_ONE
   generic map (
      DATA_WIDTH     => DATA_WIDTH,
      IMPLEMENTATION => IMPLEMENTATION
   )
   port map (
      DI => di_rot,
      DO => do_rot
   );

   --! rotate output back
   do_rot_g : for i in 0 to DATA_WIDTH-1 generate
      DO(DATA_WIDTH-1-i) <= do_rot(i);
   end generate;

end architecture;
