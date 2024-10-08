-- testbench.vhd: Testbench for tsu_async
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

   constant clkper_in      : time := 12 ns; --Clock period
   constant clkper_out     : time := 10 ns;
   constant reset_time     : time := 2*clkper_in + 1 ns; --Reset durati

   -- Clock and reset signals
   signal IN_CLK           : std_logic;
   signal OUT_CLK          : std_logic;
   signal RESET            : std_logic;

   signal IN_TS          : std_logic_vector(63 downto 0);
   signal IN_TS_DV       : std_logic;

   signal OUT_TS         : std_logic_vector(63 downto 0);
   signal OUT_TS_DV      : std_logic;

begin

   uut : entity work.tsu_async
      port map (
         IN_RESET  => RESET,
         OUT_RESET  => RESET,

         -- Input interface
         IN_CLK  => IN_CLK,

         IN_TS      => IN_TS,
         IN_TS_DV   => IN_TS_DV,

         -- Output interface
         OUT_CLK    => OUT_CLK,

         OUT_TS     => OUT_TS,
         OUT_TS_DV  => OUT_TS_DV
   );

   --Generate clock
   clk_gen_p : process
   begin
      IN_CLK <= '1';
      wait for clkper_in/2;
      IN_CLK <= '0';
      wait for clkper_in/2;
   end process clk_gen_p;

   clk_gen_p_out : process
   begin
      OUT_CLK <= '1';
      wait for clkper_out/2;
      OUT_CLK <= '0';
      wait for clkper_out/2;
   end process clk_gen_p_out;

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

      IN_TS_DV   <= '0';
      IN_TS <= (others => '0');

      wait for reset_time;
      wait for 3*clkper_in;
      wait for clkper_in;


      for I in 1 to 80 loop
            IN_TS_DV <= '1';
            IN_TS <= IN_TS + 1;
            wait for clkper_in;
      end loop;

      wait;

   end process input_flow;
end architecture;
