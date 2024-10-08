-- testbench.vhd: Testbench for ALU_DSP
-- # Copyright (C) 2014 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
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

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;
   signal A                : std_logic_vector(95 downto 0);
   signal B                : std_logic_vector(95 downto 0);
   signal CE_IN            : std_logic;
   signal CE_OUT           : std_logic;
   signal ALUMODE          : std_logic_vector(3 downto 0);
   signal CARRY_IN         : std_logic;
   signal CARRY_OUT        : std_logic;
   signal P                : std_logic_vector(95 downto 0);

begin

   uut : entity work.ALU_DSP(structural)
   generic map(
      DATA_WIDTH   => 96,
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
      ALUMODE     => ALUMODE,
      CARRY_IN    => CARRY_IN,
      CARRY_OUT   => CARRY_OUT,
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

   -- Simulating input flow
   input_flow : process
   begin

      CARRY_IN <= '0';
      ALUMODE <= "0000";
      -- Initialize input interface
      A <= (others => '0');
      B <= (others => '0');
      CE_IN <= '0';
      CE_OUT <= '0';

      wait for reset_time;
      wait for 3*clkper;

      ALUMODE <= "0000";

      A <= (1 => '1', 3 => '1', others => '0');
      B <= (0 => '1', others => '0');
      wait for clkper;

      CE_IN  <= '1';
      CE_OUT <= '1';
      wait for clkper;

      CARRY_IN <= '1';
      wait for clkper;

      CARRY_IN <= '0';
      A <= (others => '1');
      B <= (0 => '1', others => '0');
      wait for clkper;

      CARRY_IN <= '0';
      A <= (47 => '1', 94 => '1', others => '0');
      B <= (47 => '1', 94 => '1', others => '0');
      wait for clkper;

      ALUMODE <= "0001";

      A <= (1 => '1', 3 => '1', others => '0');
      B <= (0 => '1', others => '0');
      wait for clkper;

      CE_IN  <= '1';
      CE_OUT <= '1';
      wait for clkper;

      CARRY_IN <= '1';
      wait for clkper;

      CARRY_IN <= '0';
      A <= (others => '1');
      B <= (0 => '1', others => '0');
      wait for clkper;

      A <= (others => '0');
      B <= (0 => '1', others => '0');
      wait for clkper;

      ALUMODE <= "0010";

      A <= (0 => '1', 1 => '1', 2 => '1', 3 => '1', others => '0');
      A <= (0 => '1', 1 => '1', 2 => '1', 3 => '1', 4 => '1', 5 => '1', 6 => '1', 7 => '1', others => '0');
      wait for clkper;

      ALUMODE <= "0011";
      wait for clkper;

      ALUMODE <= "0100";
      wait for clkper;

      ALUMODE <= "0101";
      wait for clkper;

      ALUMODE <= "0110";
      wait for clkper;

      ALUMODE <= "0111";
      wait for clkper;

      ALUMODE <= "1000";
      wait for clkper;

      ALUMODE <= "1001";
      wait for clkper;

      ALUMODE <= "1010";
      wait for clkper;

      ALUMODE <= "1011";
      wait for clkper;

      wait;

   end process input_flow;

end architecture;
