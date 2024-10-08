-- testbench.vhd: Testbench for QDR
-- Copyright (C) 2014 CESNET
-- Author(s): Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.conv_std_logic_vector;
use IEEE.math_real.all;

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
   constant C_CLK_PER    : time := 3.0 ns;
   constant C_RESET_TIME : time := 32 ns;

   -- Signals declaration -----------------------------------------------------

   -- Synchronization
   signal clk          : std_logic;
   signal rst        : std_logic;

   -- Write request
   signal user_wr_cmd     : std_logic;
   signal user_wr_addr    : std_logic_vector(8 downto 0);
   signal user_wr_data    : std_logic_vector(143 downto 0);
   signal user_wr_bw_n    : std_logic_vector(15 downto 0);

   -- Read request
   signal user_rd_cmd     : std_logic;
   signal user_rd_addr    : std_logic_vector(8 downto 0);

   -- Output data
   signal user_rd_valid   : std_logic;
   signal user_rd_data    : std_logic_vector(143 downto 0);

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   --                              QDR_BRAM
   -- -------------------------------------------------------------------------

   -- FLU_ADAPTER instantiation
   uut: entity work.QDR_BRAM
   port map(
      --! Reset and clock -----------------------------------------------------
      CLK => clk,
      RST => rst,

      --! QDR Adapter -> QDR IP core
      --! Valid bit for data to write
      USER_WR_CMD => user_wr_cmd,
      --! Address for data to write
      USER_WR_ADDR => user_wr_addr,
      --! Data to write
      USER_WR_DATA => user_wr_data,
      --! Data write enable - active low
      USER_WR_BW_N => user_wr_bw_n,
      --! Valid bit for data to read
      USER_RD_CMD => user_rd_cmd,
      --! Address for data to read
      USER_RD_ADDR => user_rd_addr,

      --! QDR IP core -> QDR Adapter
      --! Valid bit for already read data
      USER_RD_VALID => user_rd_valid,
      --! Already read data
      USER_RD_DATA => user_rd_data

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

   -- generating rst
   rst_gen: process
   begin
      rst <= '1';
      wait for C_RESET_TIME;
      rst <= '0';
      wait;
   end process rst_gen;

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   --Simulation
   tb:process
   begin
      user_wr_cmd <= '0';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '0');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '0';
      user_rd_addr <= (others => '0');
      wait until (rst = '0');
      wait for 5*C_CLK_PER;
      wait until (clk'event and clk = '1');
      user_wr_cmd <= '1';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '1');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '0';
      user_rd_addr <= (others => '0');
      wait until (clk'event and clk = '1');
      user_wr_cmd <= '0';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '0');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '1';
      user_rd_addr <= (others => '0');
      wait until (clk'event and clk = '1');
      user_wr_cmd <= '1';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '0');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '1';
      wait until (clk'event and clk = '1');
      user_wr_cmd <= '0';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '0');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '1';
      user_rd_addr <= (others => '0');
      user_rd_addr <= (others => '0');
      wait until (clk'event and clk = '1');
      user_wr_cmd <= '0';
      user_wr_addr <= (others => '0');
      user_wr_data <= (others => '0');
      user_wr_bw_n <= (others => '0');
      user_rd_cmd <= '0';
      user_rd_addr <= (others => '0');

      wait;
   end process;

end architecture behavioral;
