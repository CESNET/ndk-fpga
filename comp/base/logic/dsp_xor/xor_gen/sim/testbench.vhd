-- testbench.vhd: Testbench for xor_gen
-- Copyright (C) 2018 CESNET
-- Author: Petr Panak <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_misc.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper      : time := 10 ns;                 -- Clock period
   constant reset_time  : time := 10*clkper + 1 ns;      -- Reset duration

   constant DATA_WIDTH  : integer := 384;                --! Data width (96, 192, 288, 384, 576, 768)

   -- Clock and reset signals
   signal CLK           : std_logic;
   signal RESET         : std_logic;

   -- Input and output
   signal DI            : std_logic_vector(DATA_WIDTH-1 downto 0);-- Data input
   signal DO_1          : std_logic;                              -- Data output
   signal DO_2          : std_logic_vector(1 downto 0);           -- Data output
   signal DO_4          : std_logic_vector(3 downto 0);           -- Data output
   signal CEI           : std_logic;                              -- Clock enable for input registers
   signal CEO           : std_logic;                              -- Clock enable for output register

   -- Signal for verification of xor function
   signal D_1           : std_logic;

begin
   -- xor_gen
   uut : entity work.xor_gen
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      IREG        => 0,
      OREG        => 0
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      DI          => DI,
      DO_1        => DO_1,
      DO_2        => DO_2,
      DO_4        => DO_4,
      CEI         => CEI,
      CEO         => CEO
   );

   -- Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   -- Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   -- Verification of xor function for DO_1 (Registers not included)
   D_1 <= xor_reduce(DI(DATA_WIDTH-1 downto DATA_WIDTH/2) & DI(DATA_WIDTH/2-1 downto 0));

   -- Simulating input flow
   input_flow : process
   begin

      -- Initialize input interface
      DI <= (others => '0'); -- output 0

      CEI   <= '1';
      CEO   <= '1';

      wait for reset_time;
      wait for 10*clkper;

      -- Data input only for 384-bit xor (Test of DO_1)
      DI <= X"0000EFEFEBCAD0000000000000000000048998484810001561935240000ABEF00000000000FFFFFFFF00FF00000000FF"; -- output 1
      wait for clkper;

      DI <= X"012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC012345689ABC"; -- output 0
      wait for clkper;

      DI <= X"264AB8695689153415BEF2A400000000000000000000000054681689300000ABB4598BCDE0000EDA00977413A0000000"; -- output 1
      wait for clkper;

      DI <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111"; -- output 0
      wait for clkper;

      DI <= X"000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"; -- output 0
      wait for clkper;

      DI <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26548613215984846516815549ABC6548613215984846516815549A1"; -- output 1
      wait for clkper;

      DI <= X"264AB8695689153415BEF2A400000000000000000000000054681689300000ABB4598BCDE0000EDA00977413A0000000"; -- output 1
      wait for clkper;

      DI <= X"ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111ABCD26891111"; -- output 0
      wait for clkper;

      -- Data input for any DATA_WIDTH (Test of DO_2, DO_4)
      for I in 0 to DATA_WIDTH-1 loop
         DI <= (others => '0');
         DI(I) <= '1';
         wait for clkper;

         report   "DO_1: "  & integer'image(conv_integer(DO_1)) &
                  " DO_2: " & integer'image(conv_integer(DO_2(1))) &
                              integer'image(conv_integer(DO_2(0))) &
                  " DO_4: " & integer'image(conv_integer(DO_4(3))) &
                              integer'image(conv_integer(DO_4(2)))&
                              integer'image(conv_integer(DO_4(1)))&
                              integer'image(conv_integer(DO_4(0)))&
                  " Bit position: " & integer'image(I);
      end loop;

      wait;

   end process input_flow;

end architecture;
