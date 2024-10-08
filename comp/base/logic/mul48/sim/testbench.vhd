-- testbench.vhd: Testbench for MUL48
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
   constant A_DATA_WIDTH   : integer := 17;
   constant B_DATA_WIDTH   : integer := 143;

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   -- input and output
   signal A                : std_logic_vector(A_DATA_WIDTH-1 downto 0);
   signal B                : std_logic_vector(B_DATA_WIDTH-1 downto 0);
   signal CE               : std_logic;
   signal P                : std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);

begin

   -- MUL48
   uut : entity work.MUL_DSP
   generic map (
      A_DATA_WIDTH => A_DATA_WIDTH,
      B_DATA_WIDTH => B_DATA_WIDTH,
      REG_IN       => 1,
      REG_OUT      => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      A           => A,
      B           => B,
      CE          => CE,
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
      A <= (others => '0');
      B <= (others => '0');
      CE <= '1';

      wait for reset_time;
      wait for 3*clkper;
      wait for clkper;

      A <= (others => '1');
      B <= (others => '1');
      wait for clkper;
      wait for clkper;
      wait for clkper;
      CE <= '0';
      wait for 20*clkper;
      CE <= '1';

      wait;

   end process input_flow;

end architecture;
