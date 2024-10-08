-- testbench.vhd: Testbench for xor8x12
-- Copyright (C) 2018 CESNET
-- Author: Petr Panak <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_misc.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper      : time := 10 ns;              -- Clock period
   constant reset_time  : time := 10*clkper + 1 ns;   -- Reset duration

   -- Clock and reset signals
   signal CLK           : std_logic;
   signal RESET         : std_logic;

   -- Input and output signals
   signal DI         : std_logic_vector(95 downto 0);    -- Data input
   signal DO_8x12    : std_logic_vector(7 downto 0);     -- Data output for 8x12-bit xor
   signal CEI        : std_logic;                        -- Clock enable for input registers
   signal CEO        : std_logic;                        -- Clock enable for output registers

   -- Signals for verification of xor function
   signal D_8x12     : std_logic_vector(7 downto 0);

begin
   -- xor8x12 entity
   uut : entity work.xor8x12(VU_DSP)
   generic map (
      IREG       => 0,
      OREG       => 0
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      DI          => DI,
      CEI         => CEI,
      CEO         => CEO,
      DO_8x12     => DO_8x12
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

   -- Verification of xor function (Registers not included)
   D_8x12(0) <= xor_reduce(DI(5 downto 0) & DI(5+48 downto 0+48));
   D_8x12(1) <= xor_reduce(DI(5+6 downto 0+6) & DI(5+48+6 downto 0+48+6));
   D_8x12(2) <= xor_reduce(DI(5+12 downto 0+12) & DI(5+48+12 downto 0+48+12));
   D_8x12(3) <= xor_reduce(DI(5+18 downto 0+18) & DI(5+48+18 downto 0+48+18));
   D_8x12(4) <= xor_reduce(DI(5+24 downto 0+24) & DI(5+48+24 downto 0+48+24));
   D_8x12(5) <= xor_reduce(DI(5+30 downto 0+30) & DI(5+48+30 downto 0+48+30));
   D_8x12(6) <= xor_reduce(DI(5+36 downto 0+36) & DI(5+48+36 downto 0+48+36));
   D_8x12(7) <= xor_reduce(DI(5+42 downto 0+42) & DI(5+48+42 downto 0+48+42));

   -- Simulating input flow
   input_flow : process
   begin

      -- Initialize input interface
      DI    <= X"000000000000000000000000";
      CEI   <= '1';
      CEO   <= '1';

      wait for reset_time;
      wait for 10*clkper;

      for I in 0 to 95 loop
         DI <= (others => '0');
         DI(I) <= '1';
         wait for clkper;

         report "DO_8x12: " & integer'image(conv_integer(DO_8x12)) &
                " Bit position: " & integer'image(I);
      end loop;

      wait;

   end process;

end architecture;
