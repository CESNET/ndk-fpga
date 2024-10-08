--! \file:   rw_registers.vhd
--! \brief:  Memory register with support BE signal
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! decoder entity
entity RW_REGISTER is
   port (
      CLK         : in  std_logic;
      --! MI32 BE signal
      BE          : in  std_logic_vector(3 downto 0);
      --! input data
      DATA        : in  std_logic_vector(31 downto 0);
      --! enbale signal
      ENABLE      : in  std_logic;
      --! reset signal
      RESET       : in  std_logic;
      --! output data
      P           : out std_logic_vector(31 downto 0)
   );
end RW_REGISTER;

--! architecture of CMP_DECODE
architecture full of RW_REGISTER is
begin
   --! 4 * 8 bit rgistes
   GEN_REG : for I in 0 to 3 generate
   begin
      gen_regs: process(CLK)
      begin
         if(CLK'event) and (CLK='1') then
            if (RESET = '1') then
               P(7+(8*I) downto 0+(8*I)) <= (others => '0');
            elsif (ENABLE = '1' and BE(I) = '1') then
               P(7+(8*I) downto 0+(8*I)) <= DATA(7+(8*I) downto 0+(8*I));
            end if;
         end if;
      end process;
   end generate;
end full;
