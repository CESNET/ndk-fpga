-- top_level_tb.vhd: FrameLink Transformer testbench file
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;
use work.fl_sim_oper.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RX_DATA_WIDTH1 : integer   := 32;
-- uncomment additional wait cycles when TX_DATA_WIDTH = 8
constant TX_DATA_WIDTH1 : integer   := 16;
constant RX_DATA_WIDTH2 : integer   := 16;
constant TX_DATA_WIDTH2 : integer   := 32;

signal CLK           : std_logic;
signal RESET         : std_logic;

signal RX_DATA1      : std_logic_vector(RX_DATA_WIDTH1-1 downto 0);
signal RX_REM1       : std_logic_vector(log2(RX_DATA_WIDTH1/8)-1 downto 0);
signal RX_SOF_N1     : std_logic;
signal RX_EOF_N1     : std_logic;
signal RX_SOP_N1     : std_logic;
signal RX_EOP_N1     : std_logic;
signal RX_SRC_RDY_N1 : std_logic;
signal RX_DST_RDY_N1 : std_logic;

signal TX_DATA1      : std_logic_vector(TX_DATA_WIDTH1-1 downto 0);
signal TX_REM1       : std_logic_vector(log2(TX_DATA_WIDTH1/8)-1 downto 0);
signal TX_SOF_N1     : std_logic;
signal TX_EOF_N1     : std_logic;
signal TX_SOP_N1     : std_logic;
signal TX_EOP_N1     : std_logic;
signal TX_SRC_RDY_N1 : std_logic;
signal TX_DST_RDY_N1 : std_logic;

signal RX_DATA2      : std_logic_vector(RX_DATA_WIDTH2-1 downto 0);
signal RX_REM2       : std_logic_vector(log2(RX_DATA_WIDTH2/8)-1 downto 0);
signal RX_SOF_N2     : std_logic;
signal RX_EOF_N2     : std_logic;
signal RX_SOP_N2     : std_logic;
signal RX_EOP_N2     : std_logic;
signal RX_SRC_RDY_N2 : std_logic;
signal RX_DST_RDY_N2 : std_logic;

signal TX_DATA2      : std_logic_vector(TX_DATA_WIDTH2-1 downto 0);
signal TX_REM2       : std_logic_vector(log2(TX_DATA_WIDTH2/8)-1 downto 0);
signal TX_SOF_N2     : std_logic;
signal TX_EOF_N2     : std_logic;
signal TX_SOP_N2     : std_logic;
signal TX_EOP_N2     : std_logic;
signal TX_SRC_RDY_N2 : std_logic;
signal TX_DST_RDY_N2 : std_logic;

-- FL Sim signals
signal filename         : t_fl_ctrl;
signal fl_sim_strobe    : std_logic;
signal fl_sim_busy      : std_logic;

begin

uut_down: entity work.FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH  => RX_DATA_WIDTH1,
      TX_DATA_WIDTH  => TX_DATA_WIDTH1
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      --
      RX_DATA        => RX_DATA1,
      RX_REM         => RX_REM1,
      RX_SOF_N       => RX_SOF_N1,
      RX_EOF_N       => RX_EOF_N1,
      RX_SOP_N       => RX_SOP_N1,
      RX_EOP_N       => RX_EOP_N1,
      RX_SRC_RDY_N   => RX_SRC_RDY_N1,
      RX_DST_RDY_N   => RX_DST_RDY_N1,
      --
      TX_DATA        => TX_DATA1,
      TX_REM         => TX_REM1,
      TX_SOF_N       => TX_SOF_N1,
      TX_EOF_N       => TX_EOF_N1,
      TX_SOP_N       => TX_SOP_N1,
      TX_EOP_N       => TX_EOP_N1,
      TX_SRC_RDY_N   => TX_SRC_RDY_N1,
      TX_DST_RDY_N   => TX_DST_RDY_N1
   );

   -- -------------------------------------------------------------------------
   --                    FL Simulation Components
   -- -------------------------------------------------------------------------
   fl_sim_uut_down: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => RX_DATA_WIDTH1,
         RX_LOG_FILE    => "",
         TX_LOG_FILE    => "",
         FRAME_PARTS    => 2
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => CLK,
         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1', -- Source isn't ready
         RX_DST_RDY_N   => open,
         TX_DATA        => RX_DATA1,
         TX_REM         => RX_REM1,
         TX_SOF_N       => RX_SOF_N1,
         TX_EOF_N       => RX_EOF_N1,
         TX_SOP_N       => RX_SOP_N1,
         TX_EOP_N       => RX_EOP_N1,
         TX_SRC_RDY_N   => RX_SRC_RDY_N1,
         TX_DST_RDY_N   => RX_DST_RDY_N1,
         -- FL SIM interface
         CTRL           => filename,
         STROBE         => fl_sim_strobe,
         BUSY           => fl_sim_busy
      );

uut_up: entity work.FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH  => RX_DATA_WIDTH2,
      TX_DATA_WIDTH  => TX_DATA_WIDTH2
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      --
      RX_DATA        => RX_DATA2,
      RX_REM         => RX_REM2,
      RX_SOF_N       => RX_SOF_N2,
      RX_EOF_N       => RX_EOF_N2,
      RX_SOP_N       => RX_SOP_N2,
      RX_EOP_N       => RX_EOP_N2,
      RX_SRC_RDY_N   => RX_SRC_RDY_N2,
      RX_DST_RDY_N   => RX_DST_RDY_N2,
      --
      TX_DATA        => TX_DATA2,
      TX_REM         => TX_REM2,
      TX_SOF_N       => TX_SOF_N2,
      TX_EOF_N       => TX_EOF_N2,
      TX_SOP_N       => TX_SOP_N2,
      TX_EOP_N       => TX_EOP_N2,
      TX_SRC_RDY_N   => TX_SRC_RDY_N2,
      TX_DST_RDY_N   => TX_DST_RDY_N2
   );

clkgen: process
   begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
   end process;

reset_gen : process
   begin
      RESET <= '1';
      wait for 1 us;
      RESET <= '0';
      wait;
   end process reset_gen;

tb: process
   -- This procedure must be placed in this testbench file. Using this
   -- procedure is necessery for corect function of FL_SIM
   procedure send_packet(ctrl : in t_fl_ctrl) is
   begin
      wait until (clk'event and clk='1' and fl_sim_busy = '0');
      filename <= ctrl;
      fl_sim_strobe <= '1';
      wait until (clk'event and clk='1');
      fl_sim_strobe <= '0';
   end send_packet;

   begin
   TX_DST_RDY_N1 <= '1';

   wait for 1 us;

   -----------------------------------------------------
   -- DOWN architecture testing
   -----------------------------------------------------
   send_packet(fl_send32("packet1.txt"));
   send_packet(fl_send32("packet1.txt"));

   wait until clk'event and clk='1';
   TX_DST_RDY_N1 <= '0';

   wait for 10*clkper;

   wait until clk'event and clk='1';
   TX_DST_RDY_N1 <= '1';
   wait until clk'event and clk='1';
   TX_DST_RDY_N1 <= '0';
   wait until clk'event and clk='1';
   TX_DST_RDY_N1 <= '1';
   wait until clk'event and clk='1';
   TX_DST_RDY_N1 <= '0';

   wait;
   end process;

end;
