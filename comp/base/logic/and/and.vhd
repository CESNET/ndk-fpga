-- and.vhd
--!
--! \file
--! \brief Generic AND.
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! \brief Generic AND entity.
entity GEN_AND is
   generic(
      --! \brief Width of input signal, number of bits to AND.
      --! \details Must be greater than 0.
      AND_WIDTH    : integer  -- and width (number of inputs)
   );
   port(
      --! Input data, vector of bits to AND.
      DI  : in  std_logic_vector(AND_WIDTH-1 downto 0);
      --! Output data, result of AND.
      DO  : out std_logic
   );
end entity;

--! \brief Behavioral implementation of generic AND.
architecture behav of GEN_AND is
begin

   --! ANDing process
   genandp:process(DI)
      variable o : std_logic;
   begin
      o := '1';
      for i in 0 to AND_WIDTH-1 loop
         o := o and DI(i);
      end loop;
      DO <= o;
   end process;

end architecture;

