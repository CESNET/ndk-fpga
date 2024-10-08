--
-- TESTBENCH.vhd: fl_sim testbench
-- Copyright (C) 2006 CESNET
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
use work.fl_sim_oper.all;
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
   constant TX_DATA_WIDTH_X : integer   := 32;
   constant RX_LOG          : string :="";
   constant TX_LOG          : string :="./tests/fl_output.txt";

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
     signal FL_bus2    : t_fl32;
     signal FL_bus3    : t_fl32;

     -- FL_SIM component ctrl
     signal fl_sim_ctrl        : t_fl_ctrl;
     signal fl_sim_strobe      : std_logic;
     signal fl_sim_busy        : std_logic;
     signal fl_sim_ctrl1        : t_fl_ctrl;
     signal fl_sim_strobe1      : std_logic;
     signal fl_sim_busy1        : std_logic;

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
FL_SIM_U : entity work.FL_SIM
   generic map (
      DATA_WIDTH=>TX_DATA_WIDTH_X,
      RX_LOG_FILE=>RX_LOG,
      TX_LOG_FILE=>TX_LOG,
      FRAME_PARTS => 3
   )
   port map (
    -- Common interface
      FL_RESET           => reset,
      FL_CLK             => fl_clk,

      -- FL Bus Interface
      RX_DATA=>FL_bus.DATA,
      RX_REM=>FL_bus.DREM, --""
      RX_SOF_N=>FL_bus.SOF_N,
      RX_EOF_N=>FL_bus.EOF_N,
      RX_SOP_N=>FL_bus.SOP_N,
      RX_EOP_N=>FL_bus.EOP_N,
      RX_SRC_RDY_N=>FL_bus.SRC_RDY_N,
      RX_DST_RDY_N=>FL_bus.DST_RDY_N,

      TX_DATA=>FL_bus2.DATA,
      TX_REM=>FL_bus2.DREM, --open
      TX_SOF_N=>FL_bus2.SOF_N,
      TX_EOF_N=>FL_bus2.EOF_N,
      TX_SOP_N=>FL_bus2.SOP_N,
      TX_EOP_N=>FL_bus2.EOP_N,
      TX_SRC_RDY_N=>FL_bus2.SRC_RDY_N,
      TX_DST_RDY_N=>FL_bus2.DST_RDY_N,

      -- IB SIM interface
      CTRL               => fl_sim_ctrl,
      STROBE             => fl_sim_strobe,
      BUSY               => fl_sim_busy
     );

MONITOR_I: entity work.MONITOR
   generic map(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH => TX_DATA_WIDTH_X,
      FILE_NAME        => "./tests/monitor.txt",
      FRAME_PARTS      => 3,
      RDY_DRIVER       => RND
   )
   port map(
      -- Common interface
      FL_RESET           => reset,
      FL_CLK             => fl_clk,

      -- RX Frame link Interface
      RX_DATA=>FL_bus2.DATA,
      RX_REM=>FL_bus2.DREM, -- ""
      RX_SOF_N=>FL_bus2.SOF_N,
      RX_EOF_N=>FL_bus2.EOF_N,
      RX_SOP_N=>FL_bus2.SOP_N,
      RX_EOP_N=>FL_bus2.EOP_N,
      RX_SRC_RDY_N=>FL_bus2.SRC_RDY_N,
      RX_DST_RDY_N=>FL_bus2.DST_RDY_N
     );


FL_BFM_U : entity work.FL_BFM
   generic map (
      DATA_WIDTH=>TX_DATA_WIDTH_X,
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

MONITOR_I1: entity work.MONITOR
   generic map(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      RX_TX_DATA_WIDTH => TX_DATA_WIDTH_X,
      FILE_NAME        => "./tests/monitor2.txt",
      FRAME_PARTS      => 3,
      RDY_DRIVER       => RND
   )
   port map(
      -- Common interface
      FL_RESET           => reset,
      FL_CLK             => fl_clk,

      -- RX Frame link Interface
      RX_DATA=>FL_bus3.DATA,
      RX_REM=>FL_bus3.DREM, -- ""
      RX_SOF_N=>FL_bus3.SOF_N,
      RX_EOF_N=>FL_bus3.EOF_N,
      RX_SOP_N=>FL_bus3.SOP_N,
      RX_EOP_N=>FL_bus3.EOP_N,
      RX_SRC_RDY_N=>FL_bus3.SRC_RDY_N,
      RX_DST_RDY_N=>FL_bus3.DST_RDY_N
     );


FL_BFM_U1 : entity work.FL_BFM
   generic map (
      DATA_WIDTH=>TX_DATA_WIDTH_X,
      FL_BFM_ID=>11
   )
   port map (
      -- Common interface
      RESET           => reset,
      CLK             => fl_clk,

      TX_DATA=>FL_bus3.DATA,
      TX_REM=>FL_bus3.DREM, -- open
      TX_SOF_N=>FL_bus3.SOF_N,
      TX_EOF_N=>FL_bus3.EOF_N,
      TX_SOP_N=>FL_bus3.SOP_N,
      TX_EOP_N=>FL_bus3.EOP_N,
      TX_SRC_RDY_N=>FL_bus3.SRC_RDY_N,
      TX_DST_RDY_N=>FL_bus3.DST_RDY_N
     );

tb : process
-- support function
procedure fl_op(ctrl : in t_fl_ctrl) is
begin
   wait until (FL_CLK'event and FL_CLK='1' and fl_sim_busy = '0');
   fl_sim_ctrl <= ctrl;
   fl_sim_strobe <= '1';
   wait until (FL_CLK'event and FL_CLK='1');
   fl_sim_strobe <= '0';
end fl_op;

begin
fl_sim_strobe <= '0';
SetSeed(5958965);
wait for reset_time;
SendWriteFile("./tests/fl_sim.txt", RND, flCmd_0, 0);
SendWriteFile("./tests/fl_sim2.txt", ONOFF, flCmd_0, 0);
--SendWriteFile("./tests/fl_sim2.txt",RND,flCmdReq,flCmdReqAck,flCmdAck,11);
--SendWriteFile("./tests/fl_sim.txt",ONOFF,flCmdReq,flCmdReqAck,flCmdAck,11);
end process;

tb2: process
begin
wait for reset_time;
SendWriteFile("./tests/fl_sim.txt", RND, flCmd_B,16#B#);
SendWriteFile("./tests/fl_sim2.txt", ONOFF, flCmd_B,16#B#);
end process;
end architecture TESTBENCH_arch;
