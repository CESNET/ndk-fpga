-- testbench.vhd: Testbench for COUNT48
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
   constant width          : integer := 128;

   constant clkper         : time := 5 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;
   -- input and output:
   signal A                : std_logic_vector(width-1 downto 0);
   signal MAX              : std_logic_vector(width-1 downto 0);
   signal ENABLE           : std_logic;
   signal P                : std_logic_vector(width-1 downto 0);

begin

   -- COUNT48
   uut : entity work.COUNT_DSP(structural)
    generic map (
      DATA_WIDTH => width,
      REG_IN  => 1,
      AUTO_RESET => 0,
      DSP_EN => false
    )
    port map (
      CLK         => CLK,
      RESET       => RESET,
      A           => A,
      MAX         => MAX,
      ENABLE      => ENABLE,
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

      ENABLE <= '0';
      --MAX <= (95 => '1', 46 => '1', others => '1');
      --A <= (49 => '1', 46 => '1', others => '0');
      MAX <= (  50 => '1', 53 => '1', 46 => '1', 49 => '1', others => '0');
      A <= (   60 => '1', 53 => '0', 46 => '1', 49 => '0', others => '0');
      wait for reset_time;
      wait for 2*clkper;

      ENABLE <= '1';
      wait for clkper;

      ENABLE <= '0';
      wait for clkper;

      ENABLE <= '1';
      wait for 2*clkper;

      ENABLE <= '0';
      wait for clkper;

    --  A <= (1 => '1', others => '0');
      ENABLE <= '0';
      wait for 6*clkper;

      ENABLE <= '1';
      wait for 2*clkper;

      ENABLE <= '0';
      wait for 2*clkper;

      ENABLE <= '1';
      wait;

   end process input_flow;

end architecture;
