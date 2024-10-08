-- testbench.vhd: Testbench for merger from n inputs to m outputs and rotate
-- Copyright (C) 2016 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
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
   constant INPUTS               : integer := 4;
   --! \brief Number of outputs
   constant OUTPUTS              : integer := 3;
   --! \brief Data width (LSB of each item is valid bit!!!)
   constant DATA_WIDTH           : integer := 3;
   --! \brief Pipe
   constant OUTPUT_REG           : boolean := false;


   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal clk                                : std_logic;
   signal rst                                : std_logic;

   signal merge_input_data                   : std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
   signal sel                                : std_logic_vector(log2(OUTPUTS)-1 downto 0);
   signal merge_output_data                  : std_logic_vector(OUTPUTS*DATA_WIDTH-1 downto 0);

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- UUT
   -- -------------------------------------------------------------------------

   uut: entity work.merge_n_to_m_rotate
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

      SEL => sel,

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
      merge_input_data((0+1)*3-1 downto (0+1)*3-2) <= "00";
      merge_input_data((1+1)*3-1 downto (1+1)*3-2) <= "01";
      merge_input_data((2+1)*3-1 downto (2+1)*3-2) <= "10";
      merge_input_data((3+1)*3-1 downto (3+1)*3-2) <= "11";
      merge_input_data(0*3)                        <= '0';
      merge_input_data(1*3)                        <= '0';
      merge_input_data(2*3)                        <= '0';
      merge_input_data(3*3)                        <= '0';
      sel <= "00";

      -- Wait for the reset
      wait until rst = '0';
      merge_input_data(0*3)                        <= '0';
      merge_input_data(1*3)                        <= '1';
      merge_input_data(2*3)                        <= '1';
      merge_input_data(3*3)                        <= '0';
      sel <= "00";
      wait for C_CLK_PER;
      merge_input_data(0*3)                        <= '0';
      merge_input_data(1*3)                        <= '0';
      merge_input_data(2*3)                        <= '0';
      merge_input_data(3*3)                        <= '1';
      sel <= "01";
      wait for C_CLK_PER;
      merge_input_data(0*3)                        <= '1';
      merge_input_data(1*3)                        <= '0';
      merge_input_data(2*3)                        <= '1';
      merge_input_data(3*3)                        <= '0';
      sel <= "10";
      wait for C_CLK_PER;
      merge_input_data(0*3)                        <= '1';
      merge_input_data(1*3)                        <= '0';
      merge_input_data(2*3)                        <= '1';
      merge_input_data(3*3)                        <= '1';
      sel <= "01";
      wait for C_CLK_PER;

      wait;
   end process;
end architecture behavioral;
