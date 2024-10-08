-- or.vhd
--!
--! \file
--! \brief Generic OR.
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2012
--!
--! \section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! \brief Generic OR entity.
entity GEN_OR is
   generic(
      --! \brief Width of input signal, number of bits to OR.
      --! \details Must be greater than 0.
      OR_WIDTH    : integer  -- or width (number of inputs)
   );
   port(
      --! Input data, vector of bits to OR.
      DI  : in  std_logic_vector(OR_WIDTH-1 downto 0);
      --! Output data, result of OR.
      DO  : out std_logic
   );
end entity;

--! \brief Behavioral implementation of generic OR.
architecture behav of GEN_OR is
begin

   --! ORing process
   genorp:process(DI)
      variable o : std_logic;
   begin
      o := '0';
      for i in 0 to OR_WIDTH-1 loop
         o := o or DI(i);
      end loop;
      DO <= o;
   end process;

end architecture;

