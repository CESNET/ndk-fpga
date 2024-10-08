-- interrupt_manager_tb.vhd: Testbench
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

-- ----------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper : time := 10 ns;
   constant reset_time : time := 10*clkper;

   signal clk            : std_logic;
   signal reset          : std_logic;
   signal interrupt_in   : std_logic_vector(31 downto 0);
   signal intr_rdy_in    : std_logic;
   signal interrupt_out  : std_logic;
   signal intr_data_out  : std_logic_vector(4 downto 0);
   signal intr_rdy_out   : std_logic;

   signal cnt_delay      : std_logic_vector(2 downto 0);

begin

   -- ------------------- Unit Under Test ----------------
   uut : entity work.interrupt_manager
   generic map(
      PULSE    => X"FFFF0000"
   )
   port map (
      CLK            => clk,
      RESET          => reset,

      INTERRUPT_IN   => interrupt_in,
      INTR_RDY_IN    => intr_rdy_in,
      INTERRUPT_OUT  => interrupt_out,
      INTR_DATA_OUT  => intr_data_out,
      INTR_RDY_OUT   => intr_rdy_out
   );

   -- ------------------- Generation of input clock -----------------
   c_gen : process
   begin
      clk <= '1';
      wait for clkper / 2;
      clk <= '0';
      wait for clkper / 2;
   end process c_gen;

   -- ------------------------ Reset generation ---------------------
   res : process
   begin
      reset<='1';
      wait for reset_time;
      reset<='0';
      wait;
   end process res;

   -- intr_rdy_out response generation
   rdy_cnt_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         cnt_delay <= "000";
      else
         if CLK'event and CLK = '1' then
            if cnt_delay = "000" then
               cnt_delay <= "101";
            elsif interrupt_out = '1' and cnt_delay = "101" then
               cnt_delay <= cnt_delay-1;
            elsif cnt_delay /= "101" then
               cnt_delay <= cnt_delay-1;
            end if;
         end if;
      end if;
   end process;

   rdy_p : process(cnt_delay)
   begin
      if cnt_delay = "101" then
         intr_rdy_out <= '1';
      else
         intr_rdy_out <= '0';
      end if;
   end process;

   -- Input requests process
   input : process
   begin

      interrupt_in <= X"00000000";

      wait for reset_time;
      wait for 1 ns;

      -- Accepted interrupt
      interrupt_in <= X"08000000";
      wait for clkper;
      interrupt_in <= X"00000000";

      wait for 2*clkper;

      -- Lost interrupt
      interrupt_in <= X"04000000";
      wait for clkper;
      interrupt_in <= X"00000000";

      wait for 7*clkper;

      -- Accepted interrupt
      interrupt_in <= X"02000000";
      wait for clkper;
      interrupt_in <= X"00000000";

      wait for 2*clkper;

      -- Not-lost interrupt
      interrupt_in <= X"01000000";
      wait until intr_rdy_out='1';
      wait for clkper;
      wait for 1 ns;
      interrupt_in <= X"00000000";

      wait for 7*clkper;

      -- Non-pulse interrupt
      interrupt_in <= X"00000001";
      wait for 8*clkper;
      interrupt_in <= X"00000000";

      -- Non-pulse interrupt
      interrupt_in <= X"00000002";
      wait for 8*clkper;
      interrupt_in <= X"00000000";

      wait;
   end process;

end behavioral;
