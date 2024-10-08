--
-- TESTBENCH.vhd: fl_fork testbench
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

   constant DATA_WIDTH : integer := 64;
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
     signal FL_bus    : t_fl64;
     signal OUT_BUS0   : t_fl64;
     signal OUT_BUS1   : t_fl64;

     -- FL_SIM component ctrl
     signal fl_sim_ctrl        : t_fl_ctrl;
     signal fl_sim_strobe      : std_logic;
     signal fl_sim_busy        : std_logic;


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
      DATA_WIDTH=>TX_DATA_WIDTH_X
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

FL_FORK641TO2_U: entity work.FL_FORK_1TO2
  generic map(
      -- Frame link width
      DATA_WIDTH=>DATA_WIDTH
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
      TX0_DATA=>OUT_BUS0.DATA,
      TX0_REM=>OUT_BUS0.DREM,
      TX0_SRC_RDY_N=>OUT_BUS0.SRC_RDY_N,
      TX0_DST_RDY_N=>OUT_BUS0.DST_RDY_N,
      TX0_SOP_N=>OUT_BUS0.SOP_N,
      TX0_EOP_N=>OUT_BUS0.EOP_N,
      TX0_SOF_N=>OUT_BUS0.SOF_N,
      TX0_EOF_N=>OUT_BUS0.EOF_N,

      TX1_DATA=>OUT_BUS1.DATA,
      TX1_REM=>OUT_BUS1.DREM,
      TX1_SRC_RDY_N=>OUT_BUS1.SRC_RDY_N,
      TX1_DST_RDY_N=>OUT_BUS1.DST_RDY_N,
      TX1_SOP_N=>OUT_BUS1.SOP_N,
      TX1_EOP_N=>OUT_BUS1.EOP_N,
      TX1_SOF_N=>OUT_BUS1.SOF_N,
      TX1_EOF_N=>OUT_BUS1.EOF_N
   );

--OUT_BUS0.DST_RDY_N<='0';
--OUT_BUS1.DST_RDY_N<='0';
prerusovac: process(CLK, RESET)
variable pom:integer;
begin
  if RESET = '1' then
    pom:=0;
  else
    if CLK'event and CLK = '1' then
     pom:=pom+1;
    end if;
  end if;
  if (pom rem 5) = 0 then
     OUT_BUS0.DST_RDY_N<='0';
   else
     OUT_BUS0.DST_RDY_N<='1';
  end if;
end process;

prerusovac2: process(CLK, RESET)
variable pom:integer;
begin
  if RESET = '1' then
    pom:=0;
  else
    if CLK'event and CLK = '1' then
     pom:=pom+1;
    end if;
  end if;
  if (pom rem 3) = 0 then
     OUT_BUS1.DST_RDY_N<='0';
   else
     OUT_BUS1.DST_RDY_N<='1';
  end if;
end process;

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
-- Testbench
fl_sim_strobe <= '0';
wait for reset_time;
fl_op(fl_send32("../../../debug/sim/sim/tests/fl_sim.txt"));
fl_op(fl_send32("../../../debug/sim/sim/tests/fl_sim2.txt"));
end process;
end architecture TESTBENCH_arch;
