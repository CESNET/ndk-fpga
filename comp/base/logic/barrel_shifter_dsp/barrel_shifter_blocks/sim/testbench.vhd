-- testbench.vhd: Testbench for BAREL_SHIFTER_DSP_TOP
-- # Copyright (C) 2015 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 1 ns; --Reset durati
   constant BLOCKS         : integer := 4;
   constant BLOCK_SIZE     : integer := 52;
   constant WIDTH_SHIFT    : integer := 4;
   constant REG_IN         : integer := 0;
   constant REG_OUT        : integer := 1;
   constant SHIFT_LEFT     : boolean := true;
   constant REGS_WITH_DSP  : boolean := true;
   constant SEL_FORMAT_SHIFT  : integer := 1;
   constant EN_ROTATE         : integer := 0;

   signal data_in_low      : std_logic_vector(3 downto 0) := X"F";
   signal data_in_high     : std_logic_vector(3 downto 0) := X"F";

   -- Clock and reset signals
   signal CLK              : std_logic;
   signal RESET            : std_logic;

   -- input and output
   signal zeros            : std_logic_vector(512 downto 0);
   signal DATA_IN          : std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
   signal DATA_OUT         : std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
   signal SHIFT_EXP        : std_logic_vector(WIDTH_SHIFT-1 downto 0);
   signal SHIFT_BINARY     : std_logic_vector(log2(WIDTH_SHIFT)-1 downto 0);
   signal CE_IN            : std_logic;
   signal CE_OUT           : std_logic;

begin
   zeros <= (others => '0');

   -- DSP_SHIFTER
   uut : entity work.BARREL_SHIFTER_BLOCKS(shift_arch)
   generic map (
      BLOCKS => BLOCKS,
      BLOCK_SIZE => BLOCK_SIZE,
      SHIFT_LEFT => SHIFT_LEFT,
      REG_IN   => REG_IN,
      REG_OUT  => REG_OUT,
      REGS_WITH_DSP => REGS_WITH_DSP,
      MAX_SHIFT => WIDTH_SHIFT,
      SEL_FORMAT_SHIFT => SEL_FORMAT_SHIFT,
      EN_ROTATE => EN_ROTATE
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      DATA_IN        => DATA_IN,
      DATA_OUT       => DATA_OUT,
      SHIFT_EXP      => SHIFT_EXP,
      SHIFT_BINARY   => SHIFT_BINARY,
      CE_IN          => '1',
      CE_OUT         => '1'
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
      DATA_IN <= (others => '0');
      SHIFT_EXP <= (others => '0');
      SHIFT_BINARY <= (others => '0');
      CE_IN <= '1';
      CE_OUT <= '1';

      wait for reset_time;
      wait for 2*clkper;

      DATA_IN <= data_in_high & zeros(BLOCKS*BLOCK_SIZE-9 downto 0) & data_in_low;
      SHIFT_EXP <= (others => '0');
      wait for clkper;

      SHIFT_EXP <= (0 => '1', others => '0');
      SHIFT_BINARY <= conv_std_logic_vector(1, SHIFT_BINARY'LENGTH);
      wait for clkper;

      SHIFT_EXP <= (1 => '1', others => '0');
      SHIFT_BINARY <= conv_std_logic_vector(2, SHIFT_BINARY'LENGTH);
      wait for clkper;

      SHIFT_EXP <= (2 => '1', others => '0');
      SHIFT_BINARY <= conv_std_logic_vector(3, SHIFT_BINARY'LENGTH);
      wait for clkper;

      SHIFT_EXP <= (3 => '1', others => '0');
      SHIFT_BINARY <= conv_std_logic_vector(4, SHIFT_BINARY'LENGTH);
      wait for clkper;

      wait;
   end process input_flow;

end architecture;
