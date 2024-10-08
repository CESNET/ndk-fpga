-- ptc_hdr_data_merge.vhd: PTC header data merge
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

entity PTC_HDR_DATA_MERGE is
   generic(
      -- =======================================================================
      -- MFB DATA BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MFB(2,1,8,32)
      MFB_REGIONS         : natural := 2;
      MFB_REGION_SIZE     : natural := 1;
      MFB_BLOCK_SIZE      : natural := 8;
      MFB_ITEM_WIDTH      : natural := 32;
      -- =======================================================================
      -- MVB HEADER BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configuration is only MVB(2,128)
      MVB_ITEMS           : natural := 2;
      MVB_ITEM_WIDTH      : natural := 128;
      -- =======================================================================
      -- OTHER CONFIGURATION:
      -- =======================================================================
      -- Width of PCIe transaction size signal. Set Log2 of maximum supported
      -- PCIe transaction size (HDR + payload) in dwords
      TRANS_SIZE_WIDTH    : natural := 8;
      -- Depth of MFB FIFO (payload data)
      MFB_FIFO_DEPTH      : natural := 32;
      -- Set correct device type, is used for choose best FIFOX settings.
      DEVICE              : string  := "ULTRASCALE";
      -- Connected PCIe endpoint type ("H_TILE" or "P_TILE") (only relevant when DEVICE=="STRATIX10")
      ENDPOINT_TYPE       : string  := "H_TILE"
   );
   port(
      -- =======================================================================
      -- CLOCK AND RESET
      -- =======================================================================
      CLK                 : in  std_logic;
      RESET               : in  std_logic;
      -- =======================================================================
      -- INPUT MVB HEADER INTERFACE
      -- =======================================================================
      -- header of PCIe transaction
      RX_MVB_DATA         : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
      -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
      RX_MVB_BE           : in  std_logic_vector(MVB_ITEMS*8-1 downto 0);
      -- is PCIe transaction with payload
      RX_MVB_PAYLOAD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- size of transaction payload, valid with RX_MVB_PAYLOAD
      RX_MVB_PAYLOAD_SIZE : in  std_logic_vector(MVB_ITEMS*TRANS_SIZE_WIDTH-1 downto 0);
      -- PCIe heade size type (Intel only) ('0' -> 96-bit type, '1' -> 128-bit type)
      RX_MVB_TYPE         : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- valid of each header of PCIe transaction in MVB word
      RX_MVB_VLD          : in  std_logic_vector(MVB_ITEMS-1 downto 0);
      -- MVB word is valid
      RX_MVB_SRC_RDY      : in  std_logic;
      -- MVB destination is ready
      RX_MVB_DST_RDY      : out std_logic;
      -- =======================================================================
      -- INPUT MFB DATA INTERFACE CONECTED DIRECTLY TO FIFO
      -- =======================================================================
      RX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      RX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      RX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      RX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
      RX_MFB_SRC_RDY      : in  std_logic;
      RX_MFB_DST_RDY      : out std_logic;
      -- =======================================================================
      -- OUTPUT MVB HEADER INTERFACE (only relevant for DEVICE="STRATIX10" and ENDPOINT_TYPE=="P_TILE")
      -- =======================================================================
      TX_MVB_DATA         : out std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
      TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
    --TX_MVB_SRC_RDY      : out std_logic; -- only TX_MFB_SRC_RDY is used
    --TX_MVB_DST_RDY      : in  std_logic; -- only TX_MFB_DST_RDY is used
      -- =======================================================================
      -- OUTPUT MFB HEADER+DATA INTERFACE (for DEVICE="STRATIX10" and ENDPOINT_TYPE=="P_TILE" the HEADER is not included here)
      -- =======================================================================
      TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
      TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
      TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
      TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
      TX_MFB_SRC_RDY      : out std_logic;
      TX_MFB_DST_RDY      : in  std_logic;
      -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
      TX_MFB_BE           : out std_logic_vector(MFB_REGIONS*8-1 downto 0)
   );
end PTC_HDR_DATA_MERGE;

architecture FULL of PTC_HDR_DATA_MERGE is

   constant MFB_REGION_WIDTH : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
   constant MFB_DATA_WIDTH   : natural := MFB_REGIONS*MFB_REGION_WIDTH;

   signal s_hdr_mvb_data    : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
   signal s_hdr_mvb_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);

   signal s_hdr_mfb_data    : std_logic_vector(MFB_DATA_WIDTH-1 downto 0);
   signal s_hdr_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
   signal s_hdr_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
   signal s_hdr_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_mfb_be      : std_logic_vector(MFB_REGIONS*8-1 downto 0);
   signal s_hdr_mfb_payload : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_mfb_type    : std_logic_vector(MFB_REGIONS-1 downto 0);
   signal s_hdr_mfb_src_rdy : std_logic;
   signal s_hdr_mfb_dst_rdy : std_logic;

begin

   -- header plan and insert
   hdr_plan_and_insert_i : entity work.PTC_HDR_DATA_MERGE_HPAI
   generic map(
      MFB_REGIONS        => MFB_REGIONS,
      MFB_REGION_SIZE    => MFB_REGION_SIZE,
      MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
      MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,
      MVB_ITEMS          => MVB_ITEMS,
      MVB_ITEM_WIDTH     => MVB_ITEM_WIDTH,
      TRANS_SIZE_WIDTH   => TRANS_SIZE_WIDTH,
      DEVICE             => DEVICE,
      ENDPOINT_TYPE      => ENDPOINT_TYPE
   )
   port map(
      CLK                 => CLK,
      RESET               => RESET,

      RX_MVB_DATA         => RX_MVB_DATA,
      RX_MVB_BE           => RX_MVB_BE,
      RX_MVB_PAYLOAD      => RX_MVB_PAYLOAD,
      RX_MVB_PAYLOAD_SIZE => RX_MVB_PAYLOAD_SIZE,
      RX_MVB_TYPE         => RX_MVB_TYPE,
      RX_MVB_VLD          => RX_MVB_VLD,
      RX_MVB_SRC_RDY      => RX_MVB_SRC_RDY,
      RX_MVB_DST_RDY      => RX_MVB_DST_RDY,

      TX_MVB_DATA         => s_hdr_mvb_data,
      TX_MVB_VLD          => s_hdr_mvb_vld,

      TX_MFB_DATA         => s_hdr_mfb_data,
      TX_MFB_SOF_POS      => s_hdr_mfb_sof_pos,
      TX_MFB_EOF_POS      => s_hdr_mfb_eof_pos,
      TX_MFB_SOF          => s_hdr_mfb_sof,
      TX_MFB_EOF          => s_hdr_mfb_eof,
      TX_MFB_BE           => s_hdr_mfb_be,
      TX_MFB_PAYLOAD      => s_hdr_mfb_payload,
      TX_MFB_TYPE         => s_hdr_mfb_type,
      TX_MFB_SRC_RDY      => s_hdr_mfb_src_rdy,
      TX_MFB_DST_RDY      => s_hdr_mfb_dst_rdy
   );

   -- insert data
   data_insert_i : entity work.PTC_HDR_DATA_MERGE_DINS
   generic map(
      MFB_REGIONS     => MFB_REGIONS,
      MFB_REGION_SIZE => MFB_REGION_SIZE,
      MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
      MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
      MFB_FIFO_DEPTH  => MFB_FIFO_DEPTH,
      DEVICE          => DEVICE,
      ENDPOINT_TYPE   => ENDPOINT_TYPE
   )
   port map(
      CLK                 => CLK,
      RESET               => RESET,

      RX_MVB_DATA         => s_hdr_mvb_data,
      RX_MVB_VLD          => s_hdr_mvb_vld,

      RX_MFB_HDR_DATA     => s_hdr_mfb_data,
      RX_MFB_HDR_SOF_POS  => s_hdr_mfb_sof_pos,
      RX_MFB_HDR_EOF_POS  => s_hdr_mfb_eof_pos,
      RX_MFB_HDR_SOF      => s_hdr_mfb_sof,
      RX_MFB_HDR_EOF      => s_hdr_mfb_eof,
      RX_MFB_HDR_BE       => s_hdr_mfb_be,
      RX_MFB_HDR_PAYLOAD  => s_hdr_mfb_payload,
      RX_MFB_HDR_TYPE     => s_hdr_mfb_type,
      RX_MFB_HDR_SRC_RDY  => s_hdr_mfb_src_rdy,
      RX_MFB_HDR_DST_RDY  => s_hdr_mfb_dst_rdy,

      RX_MFB_DATA_DATA    => RX_MFB_DATA,
      RX_MFB_DATA_SOF_POS => RX_MFB_SOF_POS,
      RX_MFB_DATA_EOF_POS => RX_MFB_EOF_POS,
      RX_MFB_DATA_SOF     => RX_MFB_SOF,
      RX_MFB_DATA_EOF     => RX_MFB_EOF,
      RX_MFB_DATA_SRC_RDY => RX_MFB_SRC_RDY,
      RX_MFB_DATA_DST_RDY => RX_MFB_DST_RDY,

      TX_MVB_DATA         => TX_MVB_DATA,
      TX_MVB_VLD          => TX_MVB_VLD,

      TX_MFB_DATA         => TX_MFB_DATA,
      TX_MFB_SOF_POS      => TX_MFB_SOF_POS,
      TX_MFB_EOF_POS      => TX_MFB_EOF_POS,
      TX_MFB_SOF          => TX_MFB_SOF,
      TX_MFB_EOF          => TX_MFB_EOF,
      TX_MFB_SRC_RDY      => TX_MFB_SRC_RDY,
      TX_MFB_DST_RDY      => TX_MFB_DST_RDY,
      TX_MFB_BE           => TX_MFB_BE
   );

end architecture;
