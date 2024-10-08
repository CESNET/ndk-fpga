-- testbench.vhd: Testbench
-- Copyright (C) 2014 CESNET
-- Author(s): Viktor Pus <pus@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH   : integer := 512;
   constant HDR_WIDTH    : integer := 32;
   constant clkper_rd    : time    := 8 ns;
   constant clkper_wr    : time    := 2 ns;

   signal clk_wr        : std_logic;
   signal rst_wr        : std_logic;
   signal rx_data       : std_logic_vector(TEST_WIDTH/2 -1 downto 0);
   signal wr            : std_logic;
   signal full          : std_logic;
   signal afull         : std_logic;
   signal clk_rd        : std_logic;
   signal rst_rd        : std_logic;
   signal tx_data       : std_logic_vector(TEST_WIDTH-1 downto 0);
   signal tx_src_rdy    : std_logic;
   signal tx_src_rdy_h  : std_logic;
   signal rx_eop        : std_logic;
   signal rx_sop        : std_logic;
   signal rx_src_rdy    : std_logic;
   signal rx_dst_rdy    : std_logic;
   signal tx_dst_rdy    : std_logic;
   signal rx_hdr        : std_logic_vector (HDR_WIDTH-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.DMAFIFO_MUX_1TO2
port map(
   -- Write interface
   CLK_WR         => clk_wr,
   RST_WR         => rst_wr,
   RX_EOP         => rx_eop,
   RX_SOP         => rx_sop,
   RX_HDR         => rx_hdr,
   RX_DATA        => rx_data,
   RX_SRC_RDY     => rx_src_rdy,
   RX_DST_RDY     => rx_dst_rdy,
   -- Read interface
   CLK_RD         => clk_rd,
   RST_RD         => rst_rd,
   TX_DATA        => tx_data,
   TX_SRC_RDY     => tx_src_rdy,
   TX_SRC_RDY_H   => tx_src_rdy_h,
   TX_DST_RDY     => tx_dst_rdy

);

-- ----------------------------------------------------
-- CLK clock generator

clk_wr_p: process
begin
   clk_wr <= '1';
   wait for clkper_wr/2;
   clk_wr <= '0';
   wait for clkper_wr/2;
end process;

clk_rd_p: process
begin
   clk_rd <= '1';
   wait for clkper_rd/2;
   clk_rd <= '0';
   wait for clkper_rd/2;
end process;

rst_wr_p: process
begin
   rst_wr <= '1';
   wait for 10*clkper_wr;
   wait for 1 ns;
   rst_wr <= '0';
   wait;
end process;

rst_rd_p: process
begin
   rst_rd <= '1';
   wait for 10*clkper_rd;
   wait for 1 ns;
   rst_rd <= '0';
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb_rd : process
begin
   tx_dst_rdy <= '0';
   wait for 37 ns;
   wait until (clk_rd'event and clk_rd='1' and rst_rd='0');
   for i in 1 to 40 loop

      wait for clkper_rd/4;
      tx_dst_rdy    <= '1';
      wait until (clk_rd'event and clk_rd='1' and rst_rd='0' and tx_src_rdy='0');
      tx_dst_rdy    <= '0';
   end loop;
   wait for 300 ns;
end process;

tb_wr : process
begin
   rx_eop <='1';
   rx_data <= (others => '0');
   wr <= '0';
   rx_hdr <= (others => '0');
   wait until (clk_wr'event and clk_wr='1' and rst_wr='0');
   rx_src_rdy <= '1';

   rx_eop <='0';
   for i in 1 to 30 loop
      rx_data <= conv_std_logic_vector(i, rx_data'length);
      rx_hdr  <= conv_std_logic_vector(i/2, rx_hdr'length);
      rx_sop  <= RX_DATA(0);
      rx_eop  <= '0';
      wait until (clk_wr'event and clk_wr='1' and RX_DST_RDY='1');
      rx_eop  <= not RX_DATA(0);
   end loop;
   rx_src_rdy <= '0';
   rx_eop     <= '1';
   rx_sop     <= '0';
   wait for 400 ns;

   wait until (clk_wr'event and clk_wr='1' and RX_DST_RDY='1');
      rx_src_rdy <= '1';
      rx_eop <= '0';
   for i in 31 to 60 loop
      rx_eop <=  (rx_data(1) xor rx_data(2));
      rx_sop <= not(rx_data(0));
      rx_data <= conv_std_logic_vector(i, rx_data'length);
      rx_hdr <= conv_std_logic_vector(i/2, rx_hdr'length);

      wait until (clk_wr'event and clk_wr='1' and RX_DST_RDY='1');
   end loop;
   rx_src_rdy <= '0';
   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
