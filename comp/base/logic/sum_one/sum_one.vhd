-- sum_one.vhd: Generic counter of one in input vector
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity SUM_ONE is
   generic(
      -- Width of input vector with ones.
      INPUT_WIDTH  : integer := 16;
      -- Output width must be log2(INPUT_WIDTH+1) or bigger.
      OUTPUT_WIDTH : integer := log2(INPUT_WIDTH+1);
      -- Enable/disable output register.
      OUTPUT_REG   : boolean := True
   );
   port(
      CLK          : in  std_logic;
      RESET        : in  std_logic;
      -- Input ports
      DIN          : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      DIN_MASK     : in  std_logic_vector(INPUT_WIDTH-1 downto 0);
      DIN_VLD      : in  std_logic;
      -- Output ports
      DOUT         : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      DOUT_VLD     : out std_logic
   );
end SUM_ONE;

architecture FULL of SUM_ONE is

   signal s_din_masked      : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal s_sum_one_comb    : unsigned(log2(INPUT_WIDTH+1)-1 downto 0);
   signal s_sum_one_reg     : unsigned(log2(INPUT_WIDTH+1)-1 downto 0);
   signal s_sum_one_vld_reg : std_logic;

begin

   -- SUM ONE assert
   assert (OUTPUT_WIDTH >= log2(INPUT_WIDTH+1))
      report "SUM_ONE: Output width must be equal log2(INPUT_WIDTH+1) or bigger!!!"
      severity failure;

   -- masking input vector
   s_din_masked <= DIN and DIN_MASK;

   -- counting ones in vector
   sum_one_comb_p : process (s_din_masked)
      variable v_tmp_value : unsigned(log2(INPUT_WIDTH+1)-1 downto 0);
   begin
      v_tmp_value := (others => '0');
      one_cnt_l : for i in 0 to INPUT_WIDTH-1 loop
         v_tmp_value := v_tmp_value + s_din_masked(i);
      end loop;
      s_sum_one_comb <= v_tmp_value;
   end process;

   -- enabled output register
   output_reg_g : if OUTPUT_REG = True generate
      sum_one_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            s_sum_one_reg <= s_sum_one_comb;
         end if;
      end process;

      valid_reg_p : process (CLK)
      begin
         if (rising_edge(CLK)) then
            if (RESET = '1') then
               s_sum_one_vld_reg <= '0';
            else
               s_sum_one_vld_reg <= DIN_VLD;
            end if;
         end if;
      end process;
   end generate;

   -- disabled output register
   no_output_reg_g : if OUTPUT_REG = False generate
      s_sum_one_reg <= s_sum_one_comb;
      s_sum_one_vld_reg <= DIN_VLD;
   end generate;

   -- output ports
   DOUT     <= std_logic_vector(resize(s_sum_one_reg,OUTPUT_WIDTH));
   DOUT_VLD <= s_sum_one_vld_reg;

end architecture;
