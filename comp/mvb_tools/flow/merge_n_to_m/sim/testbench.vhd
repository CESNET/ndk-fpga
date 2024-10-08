-- testbench.vhd: Testbench for merger from n inputs to m outputs
-- Copyright (C) 2016 CESNET
-- Author(s): Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use ieee.math_real.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- Constants declaration ---------------------------------------------------

   -- Synchronization
   constant C_CLK_PER            : time := 5.0 ns;
   constant C_RST_TIME           : time := 10 * C_CLK_PER + 1 ns;

   --! \brief Number of inputs (at most M active!!!)
   constant INPUTS               : integer := 8;
   --! \brief Number of outputs
   constant OUTPUTS              : integer := 4;
   --! \brief Data width (LSB of each item is valid bit!!!)
   constant DATA_WIDTH           : integer := 8;
   --! \brief Pipe
   constant OUTPUT_REG           : boolean := false;


   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal clk                                : std_logic;
   signal rst                                : std_logic;

   signal merge_input_data                   : std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
   signal merge_output_data                  : std_logic_vector(OUTPUTS*DATA_WIDTH-1 downto 0);

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- CROSSBAR SCHEDULER planner
   -- -------------------------------------------------------------------------

   uut: entity work.merge_n_to_m
   generic map(
      --! \brief Number of inputs (at most M active!!!)
      INPUTS => INPUTS,
      --! \brief Number of outputs
      OUTPUTS => OUTPUTS,
      --! \brief Data width (LSB of each item is valid bit!!!)
      DATA_WIDTH => DATA_WIDTH,
      --! \brief Pipe
      OUTPUT_REG => OUTPUT_REG

   )
   port map(
      --! \name Clock & reset interface
      -- --------------------------------------------------------------------------
      --! \brief Common clock
      CLK => clk,
      --! \brief Common reset
      RESET => rst,

      --! \name Input data
      -- --------------------------------------------------------------------------
      INPUT_DATA => merge_input_data,

      --! \name Ouput data
      -- --------------------------------------------------------------------------
      OUTPUT_DATA => merge_output_data
   );

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating clk
   clk_gen: process
   begin
      clk <= '1';
      wait for C_CLK_PER / 2;
      clk <= '0';
      wait for C_CLK_PER / 2;
   end process clk_gen;

   -- generating reset
   rst_gen: process
   begin
      rst <= '1';
      wait for C_RST_TIME;
      rst <= '0';
      wait;
   end process rst_gen;

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   tb: process
   begin
      -- Wait for the reset
      wait until rst = '0';
      merge_input_data <= X"0000000031211101";
      wait for C_CLK_PER;
      merge_input_data <= X"0000000000000000";
      wait for C_CLK_PER;
      merge_input_data <= X"3121110100000000";
      wait for C_CLK_PER;
      merge_input_data <= X"3100002100110100";
      wait for C_CLK_PER;

      wait;
   end process;
end architecture behavioral;
