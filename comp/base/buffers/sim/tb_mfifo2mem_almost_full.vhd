--
-- tb_mfifo2mem.vhd: ...
-- Copyright (C) 2010 CESNET
-- Author(s): Koranda Karel  <xkoran01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;

-- ---------------------------------------------------------------------
--                          ENTITY DECLARATION
-- ---------------------------------------------------------------------
entity testbench is
end entity;

-- ---------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION
-- ---------------------------------------------------------------------
architecture behavioral of testbench is

  -- constants
  constant TEST_WIDTH	: integer	:= 16;
  constant TEST_FLOWS	: integer	:= 2;
  constant TEST_BLK_S	: integer	:= 8;
  constant LUT_MEM	: boolean	:= false;
  constant OUT_REG	: boolean	:= false;
  constant clkper	: time		:= 10 ns;
  constant TEST_FL_W	: integer	:= TEST_WIDTH/TEST_FLOWS;
  constant FREE_ITEMS : integer  := 5;

  -- signals
  signal clk		: std_logic;
  signal reset		: std_logic;
  signal init		: std_logic_vector(TEST_FLOWS-1 downto 0);

  signal data_in	: std_logic_vector(TEST_WIDTH-1 downto 0);
  signal wr_blk_addr	: std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);
  signal write		: std_logic;
  signal full		: std_logic_vector(TEST_FLOWS-1 downto 0);
  signal almost_full		: std_logic_vector(TEST_FLOWS-1 downto 0);

  signal data_out	: std_logic_vector(TEST_WIDTH-1 downto 0);
  signal data_vld	: std_logic;
  signal rd_blk_addr	: std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);
  signal read		: std_logic;
  signal pipe_en	: std_logic;
  signal empty		: std_logic_vector(TEST_FLOWS-1 downto 0);

  signal rd_addr	: std_logic_vector(log2(TEST_BLK_S)-1 downto 0);
  signal rel_len	: std_logic_vector(log2(TEST_BLK_S+1)*TEST_FLOWS-1 downto 0);
  signal rel_len_dv	: std_logic_vector(TEST_FLOWS-1 downto 0);

  signal status		: std_logic_vector(log2(TEST_BLK_S+1)*TEST_FLOWS-1 downto 0);
  signal status_almost_full		: std_logic_vector(log2(TEST_BLK_S+1)*TEST_FLOWS-1 downto 0);

begin

uut : entity work.MFIFO2MEM_ALMOST_FULL
generic map(
  DATA_WIDTH 	=> TEST_WIDTH,
  FLOWS		=> TEST_FLOWS,
  BLOCK_SIZE	=> TEST_BLK_S,
  LUT_MEMORY	=> LUT_MEM,
  OUTPUT_REG	=> OUT_REG,
  FREE_ITEMS   => FREE_ITEMS
)
port map(
  CLK		=> clk,
  RESET		=> reset,
  INIT		=> init,

  DATA_IN	=> data_in,
  WR_BLK_ADDR	=> wr_blk_addr,
  WRITE		=> write,
  FULL		=> full,
  ALMOST_FULL		=> almost_full,

  DATA_OUT	=> data_out,
  DATA_VLD	=> data_vld,
  RD_BLK_ADDR	=> rd_blk_addr,
  READ		=> read,
  PIPE_EN	=> pipe_en,
  EMPTY		=> empty,

  RD_ADDR	=> rd_addr,
  REL_LEN	=> rel_len,
  REL_LEN_DV	=> rel_len_dv,

  STATUS_ALMOST_FULL	=> status_almost_full,
  STATUS	=> status
);

-- ------------------------------------------------------

-- CLK CLOCK GENERATOR
clkgen: process
begin
  clk <= '1';
  wait for clkper/2;
  clk <= '0';
  wait for clkper/2;
end process;

tb : process
begin
-- data_out <= (others => '1');
  reset <= '1';
  init <= (others => '0');
  data_in <= (others => '0');
  wr_blk_addr <= (others => '0');
  write <= '0';

  rd_blk_addr <= (others => '0');
  read <= '0';
  pipe_en <= '1';

  rd_addr <= (others => '0');
  rel_len <= (others => '0');
  rel_len_dv <= (others => '0');

  wait for clkper*8;

  reset <= '0';

  wait for clkper*4;

  wr_blk_addr <= conv_std_logic_vector(0, wr_blk_addr'length);
  write <= '1';
  for j in 1 to 20 loop
    if (j = 4) then
      wr_blk_addr <= wr_blk_addr + 1;
    end if;
    for i in 0 to TEST_FLOWS-1 loop
      data_in <= conv_std_logic_vector(j, TEST_WIDTH);
    end loop;
    wait for clkper;
  end loop;

  write <= '0';
  data_in <= conv_std_logic_vector(0, data_in'length);
  wait for 5*clkper;

  read <= '1';
  rd_blk_addr <= (others => '0');

  for j in 1 to 20 loop
    wait for clkper;
    if (j = 8) then
      rd_blk_addr <= rd_blk_addr + 1;
    end if;
    for i in 0 to TEST_FLOWS-1 loop
      rd_addr <= rd_addr + 1;
    end loop;
  end loop;

  read <= '0';
  wait for 10*clkper;
  read <= '1';

  for j in 0 to 20 loop
    wait for clkper;
    rd_blk_addr <= rd_blk_addr + 1;
    if (rd_blk_addr = TEST_FLOWS-1) then
      rd_blk_addr <= (others => '0');
    end if;
    if (j mod TEST_FLOWS = TEST_FLOWS-1) then
      rd_addr <= rd_addr + 1;
      if (rd_addr = TEST_BLK_S-1) then
        rd_addr <= (others => '0');
      end if;
    end if;
  end loop;

  read <= '0';
  wait for clkper*10;

  rel_len <= conv_std_logic_vector(3, rel_len'length);
  rel_len_dv(1) <= '0';
  rel_len_dv(0) <= '1';
  wait for 2*clkper;
  rel_len_dv <= (others => '0');
  wait for 4*clkper;
  init(1) <= '1';
  wait for 4*clkper;
end process;

end architecture behavioral;
