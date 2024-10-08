-- squarer_tb.vhd: Testbench for Squarer
-- Copyright (C) 2009 CESNET
-- Author: Ondrej Lengal <lengal@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- -------------------------------------------------------------------------
   --                               Constants
   -- -------------------------------------------------------------------------

   constant OPERAND_WIDTH         : integer := 34;
   constant RESULT_WIDTH          : integer := 68;
   constant DEGREE_OF_PARALLELISM : integer := 2;
   constant LATENCY               : integer := 1;

   -- Other constants
   constant clkper               : time := 10 ns;
   constant reset_time           : time := 100 ns;

   -- -------------------------------------------------------------------------
   --                                Signals
   -- -------------------------------------------------------------------------

   -- common interface
   signal clk       : std_logic := '0';
   signal reset     : std_logic := '1';

   -- data inputs
   signal data      : std_logic_vector(OPERAND_WIDTH-1 downto 0) := (others => '0');
   signal reg_data  : std_logic_vector(OPERAND_WIDTH-1 downto 0) := (others => '0');

   -- data output
   signal result : std_logic_vector(RESULT_WIDTH-1 downto 0) := (others => '0');


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                               Squarer
   -- -------------------------------------------------------------------------
   uut: entity work.SQUARER
   generic map
   (
      -- widths of operand
      OPERAND_WIDTH         => OPERAND_WIDTH,
      -- width of result
      RESULT_WIDTH          => RESULT_WIDTH,
      -- degree of parallelism, i.e. into how many parts will the input be split
      DEGREE_OF_PARALLELISM => DEGREE_OF_PARALLELISM,
      -- latency in clock cycles
      LATENCY               => LATENCY
   )
   port map
   (
      -- common interface
      CLK      => clk,

      -- the operand
      -- NOTE: squarer works by default as signed. For this reason, you need
      --       to set the MSB to something you don't need (it doesn't matter
      --       whether to '0' or '1' because square operation makes the result
      --       positive either way
      DATA     => data,

      -- result (is valid LATENCY clock cycles after operands are set)
      RESULT   => result
   );


   -- clock generator ---------------------------------------------------------
   clk_gen : process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   -- reset generator --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   -- counter of input data
   cnt_data_p: process (clk)
   begin
      if (rising_edge(clk)) then
         if (reset = '1') then
            data <= (others => '0');
         else
            data <= data + 100000;
         end if;
      end if;
   end process;

   -- register for saving data
   reg_data_p: process (clk)
   begin
      if (rising_edge(clk)) then
         reg_data <= data;
      end if;
   end process;

   cmp_valid_sqr_p: process (clk)
   begin
      assert ((reset = '1') OR (result = (reg_data * reg_data)))
         report "Verification failure!"
         severity failure;
   end process;



-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
begin

   wait;
end process;

end architecture;
