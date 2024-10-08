--
-- TESTBENCH.vhd: flu_bfm testbench
-- Copyright (C) 2014 CESNET
-- Author(s): Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.flu_bfm_pkg.all;
use work.flu_bfm_rdy_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end entity TESTBENCH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TESTBENCH_arch of TESTBENCH is


-- -----------------------Testbench constant-----------------------------------
   constant clkper_50       : time := 20 ns;
   constant clkper_100      : time := 10 ns;
   constant reset_time      : time := 100 * clkper_100;
   constant DATA_WIDTH      : integer  := 64;
   constant SOP_POS_WIDTH   : integer  := 3;
   constant RX_LOG          : string :="";
   constant TX_LOG          : string :="./tests/flu_output.txt";

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset             : std_logic;
   signal clk_100           : std_logic;

   -- Frame Link Unaligned inteface
   signal   tx_data       :  std_logic_vector(DATA_WIDTH-1 downto 0);
	signal   tx_sop_pos    :  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
	signal   tx_eop_pos    :  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
	signal   tx_sop        :  std_logic;
	signal   tx_eop        :  std_logic;
	signal   tx_src_rdy    :  std_logic;
	signal   tx_dst_rdy    :  std_logic;

begin

-- Reset generation -----------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

-- clk50 generator ------------------------------------------------------------
clk100_gen : process
begin
      clk_100 <= '1';
      wait for clkper_100/2;
      clk_100 <= '0';
      wait for clkper_100/2;
end process;

-- Frame Link Unaligned Bus simulation component ------------------------------
FLU_BFM_U : entity work.FLU_BFM
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      SOP_POS_WIDTH => SOP_POS_WIDTH,
      FLU_BFM_ID => 2
   )
   port map (
      -- Common interface
      RESET      => reset,
      CLK        => clk_100,

      TX_DATA    => tx_data,
      TX_SOP_POS => tx_sop_pos,
      TX_EOP_POS => tx_eop_pos,
      TX_SOP     => tx_sop,
      TX_EOP     => tx_eop,
      TX_SRC_RDY => tx_src_rdy,
      TX_DST_RDY => tx_dst_rdy
     );

MONITOR_I: entity work.MONITOR
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      SOP_POS_WIDTH => SOP_POS_WIDTH,
      FILE_NAME  => "./tests/monitor.txt",
      RDY_DRIVER => RND
   )
   port map(
      FLU_RESET  => reset,
      FLU_CLK    => clk_100,

      RX_DATA    => tx_data,
      RX_SOP_POS => tx_sop_pos,
      RX_EOP_POS => tx_eop_pos,
      RX_SOP     => tx_sop,
      RX_EOP     => tx_eop,
      RX_SRC_RDY => tx_src_rdy,
      RX_DST_RDY => tx_dst_rdy
   );

   tb2: process
   begin
      SetSeed(5958965);
      wait for reset_time;
      SendWriteFile("./tests/flu_sim.txt", RND, fluCmd_2,2);
      wait;
   end process;
end architecture TESTBENCH_arch;
