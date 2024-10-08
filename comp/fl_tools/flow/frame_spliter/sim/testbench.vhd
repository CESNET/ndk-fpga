--
-- TESTBENCH.vhd: frame_spliter testbench
-- Copyright (C) 2006 CESNET
-- Author(s):Jan Kastil <xkasti00@stud.fit.vutbr.cz>
--           Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
   constant TX_DATA_WIDTH_X : integer   := 64;
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
     signal FL_bus            : t_fl64;
     signal fl_bus_out1       : t_fl64;
     signal fl_bus_out2       : t_fl64;
     signal fl_bus1           : t_fl64;

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
      TX_LOG_FILE=>TX_LOG
   )
   port map (
      -- Common interface
      FL_RESET           => reset,
      FL_CLK             => fl_clk,

      -- FL Bus Interface
      RX_DATA=>(others => '0'),
      RX_REM=>(others => '0'),
      RX_SOF_N=>'1',
      RX_EOF_N=>'1',
      RX_SOP_N=>'1',
      RX_EOP_N=>'1',
      RX_SRC_RDY_N=>'1',
      RX_DST_RDY_N=>open,

      TX_DATA=>FL_bus.DATA,
      TX_REM=>FL_bus.DREM,
      TX_SOF_N=>FL_bus.SOF_N,
      TX_EOF_N=>FL_bus.EOF_N,
      TX_SOP_N=>FL_bus.SOP_N,
      TX_EOP_N=>FL_bus.EOP_N,
      TX_SRC_RDY_N=>FL_bus.SRC_RDY_N,
      TX_DST_RDY_N=>FL_bus.DST_RDY_N,

      -- IB SIM interface
      CTRL               => fl_sim_ctrl,
      STROBE             => fl_sim_strobe,
      BUSY               => fl_sim_busy
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
-- ready to receive

FL_bus_out1.DST_RDY_N <= '0';
FL_bus_out2.DST_RDY_N <= '0';
-- Testbench
fl_sim_strobe <= '0';
wait for reset_time;
--fl_op1(fl_log32("./tests/fl_output.txt"));
fl_op(fl_send32("./tests/fl_sim.txt"));
fl_op(fl_send32("./tests/fl_sim2.txt"));
end process;

--There is test for frame_spliter
uut: entity work.Frame_spliter
   generic map (
      fl_width_in => TX_DATA_WIDTH_X,
      fl_width_out1 => TX_DATA_WIDTH_X,
      fl_width_out2 => TX_DATA_WIDTH_X,
      Split_Pos => 2
   )
   port map(
      FL_RESET => reset,
      FL_CLK => fl_clk,
      RX_DATA => fl_bus.data,
      RX_REM => fl_bus.drem,
      RX_SOF_N =>fl_bus.sof_n,
      RX_EOF_N =>fl_bus.eof_n,
      RX_SOP_N =>fl_bus.sop_n,
      RX_EOP_N =>fl_bus.eop_n,
      RX_SRC_RDY_N =>fl_bus.src_rdy_n,
      RX_DST_RDY_N =>fl_bus.dst_rdy_n,


      TX_DATA_OUT1 => fl_bus_out1.data,
      TX_REM_OUT1 =>fl_bus_out1.drem,
      TX_SOF_N_OUT1 =>fl_bus_out1.sof_n,
      TX_EOF_N_OUT1 =>fl_bus_out1.eof_n,
      TX_SOP_N_OUT1 =>fl_bus_out1.sop_n,
      TX_EOP_N_OUT1 =>fl_bus_out1.eop_n,
      TX_SRC_RDY_N_OUT1 =>fl_bus_out1.src_rdy_n,
      TX_DST_RDY_N_OUT1 =>fl_bus_out1.dst_rdy_n,

      TX_DATA_OUT2 => fl_bus_out2.data,
      TX_REM_OUT2 =>fl_bus_out2.drem,
      TX_SOF_N_OUT2 =>fl_bus_out2.sof_n,
      TX_EOF_N_OUT2 =>fl_bus_out2.eof_n,
      TX_SOP_N_OUT2 =>fl_bus_out2.sop_n,
      TX_EOP_N_OUT2 =>fl_bus_out2.eop_n,
      TX_SRC_RDY_N_OUT2 =>fl_bus_out2.src_rdy_n,
      TX_DST_RDY_N_OUT2 =>fl_bus_out2.dst_rdy_n
   );
end architecture TESTBENCH_arch;
