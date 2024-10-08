--! last_one.vhd: Generic last one detector.
--! Copyright (C) 2018 CESNET
--! Author(s): Jakub Cabal <cabal@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

entity LAST_ONE is
   generic(
      --! \brief Width of input/output signal. Output address is one-hot encoded
      --! \details Must be greater than 0.
      DATA_WIDTH    : integer
   );
   port(
      --! Input data vector
      DI  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Output data vector - one-hot encoded
      DO  : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;

architecture FULL of LAST_ONE is

   signal di_rot : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal do_rot : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

   --! rotate input vector, first bit is last bit, etc.
   di_rot_g : for i in 0 to DATA_WIDTH-1 generate
      di_rot(DATA_WIDTH-1-i) <= DI(i);
   end generate;

   --! detect first one, output is one-hot address of first one
   first_one_i : entity work.FIRST_ONE
   generic map (
      DATA_WIDTH => DATA_WIDTH
   )
   port map (
      DI => di_rot,
      DO => do_rot
   );

   --! rotate output back => one-hot address of last one
   do_rot_g : for i in 0 to DATA_WIDTH-1 generate
      DO(DATA_WIDTH-1-i) <= do_rot(i);
   end generate;

end architecture;

