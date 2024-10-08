-- testbench.vhd: Testbench for XOR48
-- Copyright (C) 2013 CESNET
-- Author: Viktor Pus <pus@cesnet.cz>
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
   constant reset_time     : time := 10*clkper + 1 ns; --Reset duration

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   -- input and output
   signal A                : std_logic_vector(47 downto 0);
   signal B                : std_logic_vector(47 downto 0);
   signal CEAB             : std_logic;
   signal CEP              : std_logic;
   signal P                : std_logic_vector(47 downto 0);

begin

   -- XOR48
   uut : entity work.XOR48(V7_DSP)
   generic map (
      ABREG       => 1,
      PREG        => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      A           => A,
      B           => B,
      CEAB        => CEAB,
      CEP         => CEP,
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

      -- Initialize input interface
      A <= X"000000000000";
      B <= X"000000000000";
      CEAB <= '1';
      CEP <= '1';

      wait for reset_time;
      wait for 10*clkper;

      A <= X"00FF00FF00FF";
      B <= X"0F0F0F0F0F0F";
      wait for clkper;

      A <= X"0123456789AB";
      B <= X"FEDCBA987654";
      wait for clkper;

      A <= X"0123456789AB";
      B <= X"0123456789AB";
      wait for clkper;

      A <= X"EDCBA9876543";
      B <= X"FEDCBA987654";
      wait for clkper;

      wait;

   end process input_flow;

end architecture;
