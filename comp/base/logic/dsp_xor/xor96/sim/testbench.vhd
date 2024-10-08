-- testbench.vhd: Testbench for xor96
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
   signal DO_96      : std_logic;                        -- Data output for 96-bit xor
   signal DO_2x48    : std_logic_vector(1 downto 0);     -- Data output for 2x48-bit xor
   signal DO_4x24    : std_logic_vector(3 downto 0);     -- Data output for 4x24-bit xor
   signal CEI        : std_logic;                        -- Clock enable for input registers
   signal CEO        : std_logic;                        -- Clock enable for output registers

   -- Signals for verification of xor function
   signal D_96       : std_logic;                        -- Data output for 96-bit xor
   signal D_2x48     : std_logic_vector(1 downto 0);     -- Data output for 2x48-bit xor
   signal D_4x24     : std_logic_vector(3 downto 0);     -- Data output for 4x24-bit xor

begin
   -- xor96 entity
   uut : entity work.xor96(VU_DSP)
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
      DO_96       => DO_96,
      DO_2x48     => DO_2x48,
      DO_4x24     => DO_4x24
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
   D_96 <= xor_reduce(DI);
   D_2x48(0) <= xor_reduce(DI(23 downto 0) & DI(23+48 downto 48));
   D_2x48(1) <= xor_reduce(DI(23+24 downto 0+24) & DI(23+48+24 downto 48+24));
   D_4x24(0) <= xor_reduce(DI(11 downto 0) & DI(11+48 downto 48));
   D_4x24(1) <= xor_reduce(DI(11+12 downto 0+12) & DI(11+48+12 downto 48+12));
   D_4x24(2) <= xor_reduce(DI(11+24 downto 0+24) & DI(11+48+24 downto 48+24));
   D_4x24(3) <= xor_reduce(DI(11+36 downto 0+36) & DI(11+48+36 downto 48+36));

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

         report "Output 2x48: " & integer'image(conv_integer(DO_2x48)) &
                " Output 4x24: " & integer'image(conv_integer(DO_4x24)) &
                " Bit position: " & integer'image(I);
      end loop;

      wait;

   end process;

end architecture;
