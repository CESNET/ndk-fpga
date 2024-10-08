-- testbench.vhd: FrameLink Multiplexer testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <Pus@liberouter.org>
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
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RESET_TIME     : time      := 10*CLKPER + 1 ns;
constant DATA_WIDTH     : integer   := 64;
constant CHANNELS       : integer   := 4;

signal clk           : std_logic;
signal reset         : std_logic;

signal rx_data      : std_logic_vector(CHANNELS*DATA_WIDTH-1 downto 0);
signal rx_drem      : std_logic_vector((CHANNELS*log2(DATA_WIDTH/8))-1 downto 0);
signal rx_sof_n     : std_logic_vector(CHANNELS-1 downto 0);
signal rx_eof_n     : std_logic_vector(CHANNELS-1 downto 0);
signal rx_sop_n     : std_logic_vector(CHANNELS-1 downto 0);
signal rx_eop_n     : std_logic_vector(CHANNELS-1 downto 0);
signal rx_src_rdy_n : std_logic_vector(CHANNELS-1 downto 0);
signal rx_dst_rdy_n : std_logic_vector(CHANNELS-1 downto 0);

signal rx_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_drem0      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sof_n0     : std_logic;
signal rx_eof_n0     : std_logic;
signal rx_sop_n0     : std_logic;
signal rx_eop_n0     : std_logic;
signal rx_src_rdy_n0 : std_logic;
signal rx_dst_rdy_n0 : std_logic;

signal rx_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_drem1      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sof_n1     : std_logic;
signal rx_eof_n1     : std_logic;
signal rx_sop_n1     : std_logic;
signal rx_eop_n1     : std_logic;
signal rx_src_rdy_n1 : std_logic;
signal rx_dst_rdy_n1 : std_logic;

signal rx_data2      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_drem2      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sof_n2     : std_logic;
signal rx_eof_n2     : std_logic;
signal rx_sop_n2     : std_logic;
signal rx_eop_n2     : std_logic;
signal rx_src_rdy_n2 : std_logic;
signal rx_dst_rdy_n2 : std_logic;

signal rx_data3      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_drem3      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sof_n3     : std_logic;
signal rx_eof_n3     : std_logic;
signal rx_sop_n3     : std_logic;
signal rx_eop_n3     : std_logic;
signal rx_src_rdy_n3 : std_logic;
signal rx_dst_rdy_n3 : std_logic;

signal tx_channel   : std_logic_vector(log2(CHANNELS)-1 downto 0);
signal tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_drem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_sof_n     : std_logic;
signal tx_eof_n     : std_logic;
signal tx_sop_n     : std_logic;
signal tx_eop_n     : std_logic;
signal tx_src_rdy_n : std_logic;
signal tx_dst_rdy_n : std_logic_vector(CHANNELS-1 downto 0);

begin

uut: entity work.FL_MULTIPLEXER
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      CHANNELS  => CHANNELS
   )
   port map(
      CLK            => clk,
      RESET          => reset,
      --
      RX_DATA        => rx_data,
      RX_DREM        => rx_drem,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,
      --
      TX_CHANNEL     => tx_channel,
      TX_DATA        => tx_data,
      TX_DREM        => tx_drem,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n
   );

   rx_data <= rx_data3 & rx_data2 & rx_data1 & rx_data0;
   rx_drem <= rx_drem3 & rx_drem2 & rx_drem1 & rx_drem0;
   rx_sof_n <= rx_sof_n3 & rx_sof_n2 & rx_sof_n1 & rx_sof_n0;
   rx_eof_n <= rx_eof_n3 & rx_eof_n2 & rx_eof_n1 & rx_eof_n0;
   rx_sop_n <= rx_sop_n3 & rx_sop_n2 & rx_sop_n1 & rx_sop_n0;
   rx_eop_n <= rx_eop_n3 & rx_eop_n2 & rx_eop_n1 & rx_eop_n0;
   rx_src_rdy_n <= rx_src_rdy_n3 & rx_src_rdy_n2 & rx_src_rdy_n1 & rx_src_rdy_n0;
   rx_dst_rdy_n0 <= rx_dst_rdy_n(0);
   rx_dst_rdy_n1 <= rx_dst_rdy_n(1);
   rx_dst_rdy_n2 <= rx_dst_rdy_n(2);
   rx_dst_rdy_n3 <= rx_dst_rdy_n(3);

   -- -------------------------------------------------------------------------
   --                    FL Simulation Components
   -- -------------------------------------------------------------------------
FL_BFM_I0 : entity work.FL_BFM
generic map (
   DATA_WIDTH  => DATA_WIDTH,
   FL_BFM_ID   => 0)
port map (
   -- Common interface
   RESET       => reset,
   CLK         => clk,
   TX_DATA     => rx_data0,
   TX_REM      => rx_drem0,
   TX_SOF_N    => rx_sof_n0,
   TX_EOF_N    => rx_eof_n0,
   TX_SOP_N    => rx_sop_n0,
   TX_EOP_N    => rx_eop_n0,
   TX_SRC_RDY_N=> rx_src_rdy_n0,
   TX_DST_RDY_N=> rx_dst_rdy_n0);

FL_BFM_I1 : entity work.FL_BFM
generic map (
   DATA_WIDTH  => DATA_WIDTH,
   FL_BFM_ID   => 1)
port map (
   -- Common interface
   RESET       => reset,
   CLK         => clk,
   TX_DATA     => rx_data1,
   TX_REM      => rx_drem1,
   TX_SOF_N    => rx_sof_n1,
   TX_EOF_N    => rx_eof_n1,
   TX_SOP_N    => rx_sop_n1,
   TX_EOP_N    => rx_eop_n1,
   TX_SRC_RDY_N=> rx_src_rdy_n1,
   TX_DST_RDY_N=> rx_dst_rdy_n1);

FL_BFM_I2 : entity work.FL_BFM
generic map (
   DATA_WIDTH  => DATA_WIDTH,
   FL_BFM_ID   => 2)
port map (
   -- Common interface
   RESET       => reset,
   CLK         => clk,
   TX_DATA     => rx_data2,
   TX_REM      => rx_drem2,
   TX_SOF_N    => rx_sof_n2,
   TX_EOF_N    => rx_eof_n2,
   TX_SOP_N    => rx_sop_n2,
   TX_EOP_N    => rx_eop_n2,
   TX_SRC_RDY_N=> rx_src_rdy_n2,
   TX_DST_RDY_N=> rx_dst_rdy_n2);

FL_BFM_I3 : entity work.FL_BFM
generic map (
   DATA_WIDTH  => DATA_WIDTH,
   FL_BFM_ID   => 3)
port map (
   -- Common interface
   RESET       => reset,
   CLK         => clk,
   TX_DATA     => rx_data3,
   TX_REM      => rx_drem3,
   TX_SOF_N    => rx_sof_n3,
   TX_EOF_N    => rx_eof_n3,
   TX_SOP_N    => rx_sop_n3,
   TX_EOP_N    => rx_eop_n3,
   TX_SRC_RDY_N=> rx_src_rdy_n3,
   TX_DST_RDY_N=> rx_dst_rdy_n3);

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
      wait for RESET_TIME;
      RESET <= '0';
      wait;
   end process reset_gen;

tb_main:process
begin
   wait for RESET_TIME;
   tx_dst_rdy_n <= "0001";
   wait for 12*clkper;
   tx_dst_rdy_n <= "0100";
   wait for 8*clkper;
   tx_dst_rdy_n <= "0000";
   wait;
end process;

tb0: process
begin
   wait for RESET_TIME;
   wait for 5*clkper;
   SendWriteFile("./packet0.txt", EVER, flCmd_0, 0);
   wait;
end process;

tb1: process
begin
   wait for RESET_TIME;
   wait for 50*clkper;
   SendWriteFile("./packet1.txt", EVER, flCmd_1, 1);
   wait;
end process;

tb2: process
begin
   wait for RESET_TIME;
   wait for 5*clkper;
   SendWriteFile("./packet2.txt", EVER, flCmd_2, 2);
   wait;
end process;

tb3: process
begin
   wait for RESET_TIME;
   wait for 5*clkper;
   SendWriteFile("./packet3.txt", EVER, flCmd_3, 3);
   wait;
end process;

end;
