-- testbench.vhd: Testbench
-- Copyright (C) 2014 CESNET
-- Author(s): Jakub Cabal <jakubcabal@gmail.com>
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

   constant DATA_WIDTH   : integer := 512;
   constant HDR_WIDTH    : integer := 96;
   constant clkper_rd    : time    := 4 ns;
   constant clkper_wr    : time    := 7 ns;

   signal wr_clk         : std_logic;
   signal wr_rst         : std_logic;
   signal wr_dma_data    : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal wr_dma_hdr     : std_logic_vector(HDR_WIDTH - 1 downto 0);
   signal wr_dma_sop     : std_logic;
   signal wr_dma_eop     : std_logic;
   signal wr_dma_src_rdy : std_logic;
   signal wr_dma_dst_rdy : std_logic;

   signal rd_clk         : std_logic;
   signal rd_rst         : std_logic;
   signal rd_dma_data    : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal rd_dma_hdr     : std_logic_vector(HDR_WIDTH - 1 downto 0);
   signal rd_dma_sop     : std_logic;
   signal rd_dma_eop     : std_logic;
   signal rd_dma_src_rdy : std_logic;
   signal rd_dma_dst_rdy : std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.dma_asfifo_bram
generic map(
   --! \brief Width of DMA data
   DATA_WIDTH  => DATA_WIDTH,
   --! \brief Width of DMA header
   HDR_WIDTH   => HDR_WIDTH
)
port map(
   -- Write interface
   WR_CLK         => wr_clk,
   WR_RESET       => wr_rst,
   WR_DMA_DATA    => wr_dma_data,
   WR_DMA_HDR     => wr_dma_hdr,
   WR_DMA_SOP     => wr_dma_sop,
   WR_DMA_EOP     => wr_dma_eop,
   WR_DMA_SRC_RDY => wr_dma_src_rdy,
   WR_DMA_DST_RDY => wr_dma_dst_rdy,

   -- Read interface
   RD_CLK         => rd_clk,
   RD_RESET       => rd_rst,
   RD_DMA_DATA    => rd_dma_data,
   RD_DMA_HDR     => rd_dma_hdr,
   RD_DMA_SOP     => rd_dma_sop,
   RD_DMA_EOP     => rd_dma_eop,
   RD_DMA_SRC_RDY => rd_dma_src_rdy,
   RD_DMA_DST_RDY => rd_dma_dst_rdy
);

-- ----------------------------------------------------
-- CLK clock generator

clk_wr_p: process
begin
   wr_clk <= '1';
   wait for clkper_wr/2;
   wr_clk <= '0';
   wait for clkper_wr/2;
end process;

clk_rd_p: process
begin
   rd_clk <= '1';
   wait for clkper_rd/2;
   rd_clk <= '0';
   wait for clkper_rd/2;
end process;

rst_wr_p: process
begin
   wr_rst <= '1';
   wait for 10*clkper_wr;
   wait for 1 ns;
   wr_rst <= '0';
   wait;
end process;

rst_rd_p: process
begin
   rd_rst <= '1';
   wait for 10*clkper_rd;
   wait for 1 ns;
   rd_rst <= '0';
   wait;
end process;
-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb_rd : process
begin

   rd_dma_dst_rdy <= '0';
   wait until (rising_edge(rd_clk) AND rd_rst='0' AND rd_dma_src_rdy='1');

   for i in 1 to 10 loop
      rd_dma_dst_rdy    <= '1';
      wait until (rising_edge(rd_clk) AND rd_rst='0');
      rd_dma_dst_rdy    <= '0';
      wait until (rising_edge(rd_clk) AND rd_rst='0' AND rd_dma_src_rdy='1');
   end loop;

   wait for 77 ns;

   for i in 11 to 40 loop
      rd_dma_dst_rdy    <= '1';
      wait until (rising_edge(rd_clk) AND rd_rst='0');
      rd_dma_dst_rdy    <= '0';
      wait until (rising_edge(rd_clk) AND rd_rst='0' AND rd_dma_src_rdy='1');
   end loop;

   wait;

end process;

tb_wr : process
begin
   wr_dma_data    <= (others => '0');
   wr_dma_hdr     <= (others => '0');
   wr_dma_sop     <= '0';
   wr_dma_eop     <= '0';
   wr_dma_src_rdy <= '0';

   wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');

   for i in 1 to 5 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '1';
      wr_dma_eop     <= '1';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 6 to 6 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '1';
      wr_dma_eop     <= '0';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 7 to 22 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '0';
      wr_dma_eop     <= '0';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 23 to 23 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '0';
      wr_dma_eop     <= '1';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 24 to 24 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '1';
      wr_dma_eop     <= '0';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 25 to 32 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '0';
      wr_dma_eop     <= '0';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   for i in 33 to 33 loop
      wr_dma_data    <= conv_std_logic_vector(i, wr_dma_data'length);
      wr_dma_hdr     <= conv_std_logic_vector(i, wr_dma_hdr'length);
      wr_dma_sop     <= '0';
      wr_dma_eop     <= '1';
      wr_dma_src_rdy <= '1';
      wait until (rising_edge(wr_clk) AND wr_rst='0' AND wr_dma_dst_rdy='1');
   end loop;

   wr_dma_src_rdy <= '0';

   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
