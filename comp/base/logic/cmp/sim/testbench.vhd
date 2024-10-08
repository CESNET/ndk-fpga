--! testbench.vhd: Testbench for CMP48
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

entity testbench is

end testbench;

architecture behavioral of testbench is


   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati

   --! Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   --! input and output
   signal A                : std_logic_vector(129 downto 0);
   signal B                : std_logic_vector(129 downto 0);
   signal CE_IN            : std_logic;
   signal CE_OUT           : std_logic;
   signal P                : std_logic_vector(1 downto 0);

begin

   --! CMP48
   uut : entity work.CMP_DSP(structural)
   generic map (
      DATA_WIDTH   => 130,
      REG_IN       => 1,
      REG_OUT      => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      A           => A,
      B           => B,
      CE_IN       => CE_IN,
      CE_OUT      => CE_OUT,
      P           => P
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
      A <= (others => '0');
      B <= (others => '0');
      CE_IN <= '0';
      CE_OUT <= '0';

      wait for reset_time;
      wait for 3*clkper;
      wait for clkper;

      A <= (24 => '0', others => '1');
      B <= (others => '1');
      wait for clkper;

      CE_IN <= '1';
      CE_OUT <= '1';
      wait for clkper;

      A <= (  105 => '1', 84 => '0', 1 => '1', 30 => '0', others => '0');
      B <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
      wait for clkper;

      A <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
      B <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
      wait for clkper;

      A <= (  105 => '1', 84 => '1', 1 => '1', 30 => '0', others => '0');
      B <= (  105 => '1', 84 => '1', 0 => '1', 30 => '0', others => '0');
      wait for clkper;

      A <= (  105 => '0', 84 => '1', 1 => '1', 30 => '0', others => '0');
      B <= (  105 => '1', 84 => '1', 0 => '1', 30 => '0', others => '0');
      wait for clkper;

      A <= (  105 => '1', 84 => '1', 45 => '1', 30 => '1', others => '0');
      B <= (  105 => '1', 84 => '1', 45 => '1', 30 => '1', others => '0');
      wait for clkper;

      wait;

   end process input_flow;
end architecture;
