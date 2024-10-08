--! testbench.vhd: Testbench for PIPE
--! Copyright (C) 2015 CESNET
--! Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--!
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
   --! generic parameters
   constant DATA_WIDTH     : integer := 20;
   constant NUM_REGS       : integer := 1;
   --! Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;
   --! input and output
   signal DATA_IN          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal DATA_OUT         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal CE               : std_logic;

begin

   uut: entity work.PIPE_DSP
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      NUM_REGS => NUM_REGS,
      ENABLE_DSP => true,
      PIPE_EN => false
   )
   port map (
      CLK => CLK,
      RESET => RESET,
      DATA_IN => DATA_IN,
      DATA_OUT => DATA_OUT,
      CE => CE
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
      DATA_IN <= (others => '0');
      CE <= '1';

      wait for reset_time;
      wait for 3*clkper;
      wait for clkper;

      DATA_IN <= conv_std_logic_vector(1, DATA_IN'LENGTH);
      wait for clkper;

      DATA_IN <= conv_std_logic_vector(2, DATA_IN'LENGTH);
      wait for clkper;

      DATA_IN <= conv_std_logic_vector(3, DATA_IN'LENGTH);
      wait for clkper;

      wait;

   end process input_flow;
end architecture;
