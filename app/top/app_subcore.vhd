-- app_subcore.vhd: User application subcore
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Vladislav Vlake <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;

entity APP_SUBCORE is
    generic (
        MI_WIDTH : natural := 32;

        -- MFB parameters
        MFB_REGIONS     : integer := 1;  -- Number of regions in word
        MFB_REGION_SIZE : integer := 8;  -- Number of blocks in region
        MFB_BLOCK_SIZE  : integer := 8;  -- Number of items in block
        MFB_ITEM_WIDTH  : integer := 8;  -- Width of one item in bits

        -- Maximum size of a User packet (in bytes)
        -- Defines width of Packet length signals.
        USR_PKT_SIZE_MAX : natural := 2**12;

        -- Number of streams from DMA module
        DMA_RX_CHANNELS : integer;
        DMA_TX_CHANNELS : integer;

        -- Width of TX User Header Metadata information extracted from descriptor
        DMA_HDR_META_WIDTH : natural := 12;

        DEVICE : string := "ULTRASCALE"
        );
    port (
        -- =========================================================================
        -- Clock and Resets inputs
        -- =========================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =====================================================================
        -- TX DMA User-side MFB
        -- =====================================================================
        DMA_TX_MFB_META_PKT_SIZE : in std_logic_vector(log2(USR_PKT_SIZE_MAX + 1) -1 downto 0);
        DMA_TX_MFB_META_HDR_META : in std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
        DMA_TX_MFB_META_CHAN     : in std_logic_vector(log2(DMA_TX_CHANNELS) -1 downto 0);

        DMA_TX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        DMA_TX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_TX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_TX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
        DMA_TX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        DMA_TX_MFB_SRC_RDY : in  std_logic;
        DMA_TX_MFB_DST_RDY : out std_logic := '1';

        -- =====================================================================
        -- RX DMA User-side MFB
        -- =====================================================================
        DMA_RX_MFB_META_PKT_SIZE : out std_logic_vector(log2(USR_PKT_SIZE_MAX + 1) -1 downto 0);
        DMA_RX_MFB_META_HDR_META : out std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
        DMA_RX_MFB_META_CHAN     : out std_logic_vector(log2(DMA_RX_CHANNELS) -1 downto 0);

        DMA_RX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        DMA_RX_MFB_SOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_RX_MFB_EOF     : out std_logic_vector(MFB_REGIONS -1 downto 0);
        DMA_RX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
        DMA_RX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        DMA_RX_MFB_SRC_RDY : out std_logic;
        DMA_RX_MFB_DST_RDY : in  std_logic;

        -- =========================================================================
        --  MI INTERFACE
        -- =========================================================================
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
        );
end entity;

architecture FULL of APP_SUBCORE is

begin

    MI_DRD  <= (others => '0');
    MI_ARDY <= MI_RD or MI_WR;
    MI_DRDY <= MI_RD;

    DMA_RX_MFB_META_PKT_SIZE <= DMA_TX_MFB_META_PKT_SIZE;
    DMA_RX_MFB_META_HDR_META <= DMA_TX_MFB_META_HDR_META;
    DMA_RX_MFB_META_CHAN     <= DMA_TX_MFB_META_CHAN;

    DMA_RX_MFB_DATA    <= DMA_TX_MFB_DATA;
    DMA_RX_MFB_SOF     <= DMA_TX_MFB_SOF;
    DMA_RX_MFB_EOF     <= DMA_TX_MFB_EOF;
    DMA_RX_MFB_SOF_POS <= DMA_TX_MFB_SOF_POS;
    DMA_RX_MFB_EOF_POS <= DMA_TX_MFB_EOF_POS;
    DMA_RX_MFB_SRC_RDY <= DMA_TX_MFB_SRC_RDY;
    DMA_TX_MFB_DST_RDY <= DMA_RX_MFB_DST_RDY;
end architecture;
