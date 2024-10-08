--! testbench.vhd: Testbench for MUX_DSP
--! # Copyright (C) 2014 CESNET
--! # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.math_pack.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati
   constant data_width     : integer := 8;
   constant mux_width      : integer := 8;

   --! Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   --! input and output
   signal DATA_IN          : std_logic_vector(data_width*mux_width-1 downto 0);
   signal CE_IN            : std_logic;
   signal CE_LVL           : std_logic;
   signal SEL              : std_logic_vector(log2(mux_width)-1 downto 0);
   signal CE_OUT           : std_logic;
   signal DATA_OUT         : std_logic_vector(data_width-1 downto 0);

begin

   --! MUX_DSP
   uut : entity work.MUX_DSP_GEN
   generic map (
      DATA_WIDTH  => data_width,
      MUX_WIDTH   => mux_width,
      REG_IN      => 1,
      REG_OUT     => 0,
      REG_LVL     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      DATA_IN     => DATA_IN,
      CE_IN       => CE_IN,
      CE_LVL      => CE_LVL,
      CE_OUT      => CE_OUT,
      SEL         => SEL,
      DATA_OUT    => DATA_OUT
   );

   --Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   --Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   --! Simulating input flow
   input_flow : process
   begin

      --! Initialize input interface
      CE_IN    <= '1';
      CE_LVL   <= '1';
      CE_OUT   <= '1';
      DATA_IN  <= X"0011223344556677";
      SEL <= "000";

      wait for reset_time;
      wait for clkper;

      SEL <= "001";
      wait for clkper;
      SEL <= "010";
      wait;

   end process input_flow;
end architecture;
