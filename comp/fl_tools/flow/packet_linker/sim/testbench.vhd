--
-- TESTBENCH.vhd: packet_linker testbench
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use work.fl_pkg.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

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
   constant TX_DATA_WIDTH   : integer := 32;

-- -----------------------Testbench auxilarity signals-------------------------
     -- CLK_GEN Signals
     signal reset             : std_logic;
     signal clk               : std_logic;
     signal clk_50_in         : std_logic;
     signal clk50             : std_logic;
     signal clk100            : std_logic;
     signal lock              : std_logic;
     signal fl_clk            : std_logic;

     -- Frame Link Bus 32 (FL_SIM)
     signal FL_bus    : t_fl32;
     signal OUT_BUS   : t_fl32;




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
clk50_gen : process
begin
   clk_50_in <= '1';
   wait for clkper_50/2;
   clk_50_in <= '0';
   wait for clkper_50/2;
end process;

-- CLK_GEN component ----------------------------------------------------------
CLK_GEN_U: entity work.CLK_GEN
   port map (
      -- Input
      CLK50_IN    => clk_50_in,
      RESET       => '0',
      -- Output
      CLK50_OUT   => clk50,
      CLK25       => open,
      CLK100      => clk100,
      CLK200      => open,
      LOCK        => lock
   );
clk <= clk100;
fl_clk <= clk100;

-- Frame Link Bus simulation component ------------------------------------------
FL_BFM_U : entity work.FL_BFM
   generic map (
      DATA_WIDTH=>TX_DATA_WIDTH,
      FL_BFM_ID=>0
   )
   port map (
      -- Common interface
      RESET           => reset,
      CLK             => fl_clk,

      TX_DATA=>FL_bus.DATA,
      TX_REM=>FL_bus.DREM, -- open
      TX_SOF_N=>FL_bus.SOF_N,
      TX_EOF_N=>FL_bus.EOF_N,
      TX_SOP_N=>FL_bus.SOP_N,
      TX_EOP_N=>FL_bus.EOP_N,
      TX_SRC_RDY_N=>FL_bus.SRC_RDY_N,
      TX_DST_RDY_N=>FL_bus.DST_RDY_N
     );

PACKET_LINKER_U: entity work.PACKET_LINKER
  generic map(
      PACKET_ID => 1
      )
   port map(
      CLK=>FL_CLK,
      RESET=>RESET,
      -- Input Interface
      RX_DATA=>FL_bus.DATA,
      RX_REM=>FL_bus.DREM,
      RX_SRC_RDY_N=>FL_bus.SRC_RDY_N,
      RX_DST_RDY_N=>FL_bus.DST_RDY_N,
      RX_SOP_N=>FL_bus.SOP_N,
      RX_EOP_N=>FL_bus.EOP_N,
      RX_SOF_N=>FL_bus.SOF_N,
      RX_EOF_N=>FL_bus.EOF_N,

      -- Output Interface
      TX_DATA=>OUT_BUS.DATA,
      TX_REM=>OUT_BUS.DREM,
      TX_SRC_RDY_N=>OUT_BUS.SRC_RDY_N,
      TX_DST_RDY_N=>OUT_BUS.DST_RDY_N,
      TX_SOP_N=>OUT_BUS.SOP_N,
      TX_EOP_N=>OUT_BUS.EOP_N,
      TX_SOF_N=>OUT_BUS.SOF_N,
      TX_EOF_N=>OUT_BUS.EOF_N
   );

MONITOR_I: entity work.MONITOR
   generic map(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH => TX_DATA_WIDTH,
      FILE_NAME        => "./tests/monitor.txt",
      FRAME_PARTS      => 3,
      RDY_DRIVER       => ONOFF
   )
   port map(
      -- Common interface
      FL_RESET           => reset,
      FL_CLK             => fl_clk,

      -- RX Frame link Interface
      RX_DATA=>OUT_BUS.DATA,
      RX_REM=>OUT_BUS.DREM, -- ""
      RX_SOF_N=>OUT_BUS.SOF_N,
      RX_EOF_N=>OUT_BUS.EOF_N,
      RX_SOP_N=>OUT_BUS.SOP_N,
      RX_EOP_N=>OUT_BUS.EOP_N,
      RX_SRC_RDY_N=>OUT_BUS.SRC_RDY_N,
      RX_DST_RDY_N=>OUT_BUS.DST_RDY_N
     );

tb : process


begin
-- Testbench
wait for reset_time;
SetSeed(4878);
SendWriteFile("./tests/test3.txt", RND, flCmd_0, 0);
end process;
end architecture TESTBENCH_arch;
