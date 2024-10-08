-- mfb_duplication.vhd: Simple duplication MFB bus
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_DUPLICATION is
   generic(
      REGIONS     : natural := 4;
      REGION_SIZE : natural := 8;
      BLOCK_SIZE  : natural := 8;
      ITEM_WIDTH  : natural := 8
   );
   port(
      -- CLOCK AND RESET
      CLK         : in  std_logic;
      RST         : in  std_logic;
      -- RX MFB INTERFACE
      RX_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY  : in  std_logic;
      RX_DST_RDY  : out std_logic;
      -- TX MFB INTERFACE #0
      TX0_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX0_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX0_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX0_SOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX0_EOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX0_SRC_RDY : out std_logic;
      TX0_DST_RDY : in  std_logic;
      -- TX MFB INTERFACE #1
      TX1_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX1_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX1_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX1_SOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX1_EOF     : out std_logic_vector(REGIONS-1 downto 0);
      TX1_SRC_RDY : out std_logic;
      TX1_DST_RDY : in  std_logic
   );
end MFB_DUPLICATION;

architecture FULL of MFB_DUPLICATION is

   signal s_rx_dst_rdy  : std_logic;

   signal s_tx0_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   signal s_tx0_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal s_tx0_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal s_tx0_sof     : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx0_eof     : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx0_src_rdy : std_logic;

   signal s_tx1_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   signal s_tx1_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   signal s_tx1_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   signal s_tx1_sof     : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx1_eof     : std_logic_vector(REGIONS-1 downto 0);
   signal s_tx1_src_rdy : std_logic;

begin

   -- --------------------------------------------------------------------------
   --  MFB DUPLICATION LOGIC
   -- --------------------------------------------------------------------------

   s_rx_dst_rdy  <= TX0_DST_RDY and TX1_DST_RDY;

   s_tx0_data    <= RX_DATA;
   s_tx0_sof_pos <= RX_SOF_POS;
   s_tx0_eof_pos <= RX_EOF_POS;
   s_tx0_sof     <= RX_SOF;
   s_tx0_eof     <= RX_EOF;
   s_tx0_src_rdy <= TX1_DST_RDY and RX_SRC_RDY;

   s_tx1_data    <= RX_DATA;
   s_tx1_sof_pos <= RX_SOF_POS;
   s_tx1_eof_pos <= RX_EOF_POS;
   s_tx1_sof     <= RX_SOF;
   s_tx1_eof     <= RX_EOF;
   s_tx1_src_rdy <= TX0_DST_RDY and RX_SRC_RDY;

   -- --------------------------------------------------------------------------
   --  ASSIGNMENT OF OUTPUTS
   -- --------------------------------------------------------------------------

   RX_DST_RDY  <= s_rx_dst_rdy;

   TX0_DATA    <= s_tx0_data;
   TX0_SOF_POS <= s_tx0_sof_pos;
   TX0_EOF_POS <= s_tx0_eof_pos;
   TX0_SOF     <= s_tx0_sof;
   TX0_EOF     <= s_tx0_eof;
   TX0_SRC_RDY <= s_tx0_src_rdy;

   TX1_DATA    <= s_tx1_data;
   TX1_SOF_POS <= s_tx1_sof_pos;
   TX1_EOF_POS <= s_tx1_eof_pos;
   TX1_SOF     <= s_tx1_sof;
   TX1_EOF     <= s_tx1_eof;
   TX1_SRC_RDY <= s_tx1_src_rdy;

end architecture;
