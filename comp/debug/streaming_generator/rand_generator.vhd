--! \file:   rand_generator.vhd
--! \brief:  Generated random values
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
use IEEE.STD_LOGIC_1164.ALL;

entity RAND_GENERATOR is
   generic (
      --! Data width of input/output value
      DATA_WIDTH  : integer :=  32
   );
   port (
      CLK         : in std_logic;
      RAND_OUT    : out std_logic_vector (DATA_WIDTH-1 downto 0)   --output vector
    );
end RAND_GENERATOR;

architecture full of RAND_GENERATOR is
begin
   gen_rand_value: process(CLK)
      variable rand_temp : std_logic_vector(DATA_WIDTH-1 downto 0):=(DATA_WIDTH-1 => '1',others => '0');
      variable temp      : std_logic := '0';
   begin
      --! generating random value
      if (CLK'event) and (CLK='1') then
         temp := rand_temp(DATA_WIDTH-1) xor rand_temp(DATA_WIDTH-2);
         rand_temp(DATA_WIDTH-1 downto 1) := rand_temp(DATA_WIDTH-2 downto 0);
         rand_temp(0) := temp;
      end if;
      RAND_OUT <= rand_temp;
   end process;
end full;
