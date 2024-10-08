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

   --! \brief Data width
   constant DATA_WIDTH           : integer := 15;

   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal clk                                : std_logic;
   signal rst                                : std_logic;

   signal n_one_d                            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal n_one_n                            : std_logic_vector(log2(DATA_WIDTH)-1 downto 0);
   signal n_one_a                            : std_logic_vector(log2(DATA_WIDTH)-1 downto 0);
   signal n_one_vld                          : std_logic;


-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- CROSSBAR SCHEDULER planner
   -- -------------------------------------------------------------------------

   uut: entity work.n_one
   generic map(
      --! \brief Data width of input vector
      DATA_WIDTH => DATA_WIDTH
   )
   port map(

      --! \name Clock & reset interface
      --! --------------------------------------------------------------------------
      --! \brief Common clock
      CLK => clk,
      --! \brief Common reset
      RESET => rst,

      --! \name Input vector
      --! --------------------------------------------------------------------------
      D => n_one_d,

      --! \name N one number
      --! -------------------------------------------------------------------------
      N => n_one_n,

      --! \name Output address
      --! --------------------------------------------------------------------------
      A => n_one_a,
      --! \brief Valid bit
      VLD => n_one_vld

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

   tb: process
   begin
      -- Wait for the reset
      wait until rst = '0';
      n_one_d <= "000" & X"F00";
      n_one_n <= X"4";
      wait for C_CLK_PER;
      n_one_d <= "111" & X"FFF";
      n_one_n <= X"F";
      wait for C_CLK_PER;
      n_one_d <= "000" & X"000";
      n_one_n <= X"0";
      wait for C_CLK_PER;
      n_one_d <= "000" & X"F1B";
      n_one_n <= X"5";
      wait for C_CLK_PER;
      n_one_d <= "111"  & X"01C";
      n_one_n <= X"3";
      wait for C_CLK_PER;
      n_one_d <= "111" & X"01C";
      n_one_n <= X"0";
      wait for C_CLK_PER;
      n_one_d <= "111" & X"31C";
      n_one_n <= X"8";
      wait for C_CLK_PER;
      n_one_d <= "111" & X"30C";
      n_one_n <= X"6";

      wait;
   end process;
end architecture behavioral;
