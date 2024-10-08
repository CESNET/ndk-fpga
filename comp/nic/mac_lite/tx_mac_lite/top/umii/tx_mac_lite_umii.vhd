-- tx_mac_lite_umii.vhd: TX MAC Lite top level module with Universal MII encoder
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_UMII is
    generic(
        -- =====================================================================
        -- MII CONFIGURATION:
        -- =====================================================================
        -- Data width of MII data signal, must be power of two, minimum is 64
        MII_DW          : natural := 2048;
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        -- By default the RX parameters are calculated automatically from MII_DW.
        -- Useful for narrowing data width from 512b (RX) to 64b (MII).
        RX_REGIONS      : natural := max(MII_DW/512,1);
        RX_BLOCK_SIZE   : natural := 8; -- SOF must be aligned by 8 bytes
        RX_ITEM_WIDTH   : natural := 8; -- must be 8, one item = one byte
        RX_REGION_SIZE  : natural := (MII_DW/RX_REGIONS)/(RX_BLOCK_SIZE*RX_ITEM_WIDTH);
        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================
        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Set true when CRC checksum is included in frames on RX MFB stream.
        RX_INCLUDE_CRC  : boolean := False;
        -- Set true when free items for CRC checksum (when RX_INCLUDE_CRC=false)
        -- and Inter Packet Gaps (IPG) are included on RX MFB stream.
        RX_INCLUDE_IPG  : boolean := True;
        -- Set true when you need use counters implemented in DSP.
        USE_DSP_CNT     : boolean := False;
        -- FPGA device name.
        DEVICE          : string := "STRATIX10"
    );
    port(
        -- =====================================================================
        --  MI32 INTERFACE (MI_CLK)
        -- =====================================================================
        MI_CLK         : in  std_logic;
        MI_RESET       : in  std_logic;
        MI_DWR         : in  std_logic_vector(31 downto 0);
        MI_ADDR        : in  std_logic_vector(31 downto 0);
        MI_RD          : in  std_logic;
        MI_WR          : in  std_logic;
        MI_BE          : in  std_logic_vector(3 downto 0);
        MI_DRD         : out std_logic_vector(31 downto 0);
        MI_ARDY        : out std_logic;
        MI_DRDY        : out std_logic;

        -- =====================================================================
        --  RX MFB INPUT STREAM
        -- =====================================================================
        RX_CLK         : in  std_logic;
        RX_CLK_X2      : in  std_logic;
        RX_RESET       : in  std_logic;
        RX_MFB_DATA    : in  std_logic_vector(RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- OUTPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...)
        -- =====================================================================
        MII_CLK        : in  std_logic;
        MII_RESET      : in  std_logic;
        -- MII signal with data bits
        MII_TXD        : out std_logic_vector(MII_DW-1 downto 0);
        -- MII signal with control flags
        MII_TXC        : out std_logic_vector(MII_DW/8-1 downto 0);
        -- Valid signal of MII word (optional).
        MII_VLD        : out std_logic;
        -- Ready signal of MII word, set to VCC if this signal is not needed.
        MII_RDY        : in  std_logic := '1';

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE (MII_CLK)
        -- =====================================================================
        -- Active during frame transmission
        OUTGOING_FRAME : out std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_UMII is

    -- The TX MFB parameters are calculated automatically from MII configuration
    constant TX_REGIONS     : natural := max(MII_DW/512,1);
    constant TX_BLOCK_SIZE  : natural := tsel(MII_DW=64,4,8);
    constant TX_ITEM_WIDTH  : natural := 8;
    constant TX_REGION_SIZE : natural := (MII_DW/TX_REGIONS)/(TX_BLOCK_SIZE*8);

    signal mac_mfb_data       : std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
    signal mac_mfb_sof_pos    : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
    signal mac_mfb_eof_pos    : std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
    signal mac_mfb_sof        : std_logic_vector(TX_REGIONS-1 downto 0);
    signal mac_mfb_eof        : std_logic_vector(TX_REGIONS-1 downto 0);
    signal mac_mfb_src_rdy    : std_logic;
    signal mac_mfb_dst_rdy    : std_logic;

begin

    tx_mac_lite_i : entity work.TX_MAC_LITE
    generic map(
        TX_REGIONS      => TX_REGIONS,
        TX_REGION_SIZE  => TX_REGION_SIZE,
        TX_BLOCK_SIZE   => TX_BLOCK_SIZE,
        TX_ITEM_WIDTH   => TX_ITEM_WIDTH,
        RX_REGIONS      => RX_REGIONS,
        RX_REGION_SIZE  => RX_REGION_SIZE,
        RX_BLOCK_SIZE   => RX_BLOCK_SIZE,
        RX_ITEM_WIDTH   => RX_ITEM_WIDTH,
        PKT_MTU_BYTES   => PKT_MTU_BYTES,
        RX_INCLUDE_CRC  => RX_INCLUDE_CRC,
        RX_INCLUDE_IPG  => RX_INCLUDE_IPG,
        CRC_INSERT_EN   => not RX_INCLUDE_CRC,
        IPG_GENERATE_EN => not RX_INCLUDE_IPG,
        USE_DSP_CNT     => USE_DSP_CNT,
        ETH_VERSION     => tsel((MII_DW=64),"10Gb","over10Gb"),
        DEVICE          => DEVICE
    )
    port map(
        MI_CLK         => MI_CLK,
        MI_RESET       => MI_RESET,
        MI_DWR         => MI_DWR,
        MI_ADDR        => MI_ADDR,
        MI_RD          => MI_RD,
        MI_WR          => MI_WR,
        MI_BE          => MI_BE,
        MI_DRD         => MI_DRD,
        MI_ARDY        => MI_ARDY,
        MI_DRDY        => MI_DRDY,

        RX_CLK         => RX_CLK,
        RX_CLK_X2      => RX_CLK_X2,
        RX_RESET       => RX_RESET,
        RX_MFB_DATA    => RX_MFB_DATA,
        RX_MFB_SOF_POS => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS => RX_MFB_EOF_POS,
        RX_MFB_SOF     => RX_MFB_SOF,
        RX_MFB_EOF     => RX_MFB_EOF,
        RX_MFB_SRC_RDY => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY => RX_MFB_DST_RDY,

        TX_CLK         => MII_CLK,
        TX_RESET       => MII_RESET,
        TX_MFB_DATA    => mac_mfb_data,
        TX_MFB_SOF_POS => mac_mfb_sof_pos,
        TX_MFB_EOF_POS => mac_mfb_eof_pos,
        TX_MFB_SOF     => mac_mfb_sof,
        TX_MFB_EOF     => mac_mfb_eof,
        TX_MFB_SRC_RDY => mac_mfb_src_rdy,
        TX_MFB_DST_RDY => mac_mfb_dst_rdy,

        OUTGOING_FRAME => OUTGOING_FRAME
    );

    umii_enc_i : entity work.UMII_ENC
    generic map(
        MII_DW      => MII_DW,
        REGIONS     => TX_REGIONS,
        BLOCK_SIZE  => TX_BLOCK_SIZE,
        ITEM_WIDTH  => TX_ITEM_WIDTH,
        REGION_SIZE => TX_REGION_SIZE
    )
    port map(
        CLK        => MII_CLK,
        RESET      => MII_RESET,

        RX_DATA    => mac_mfb_data,
        RX_SOF_POS => mac_mfb_sof_pos,
        RX_EOF_POS => mac_mfb_eof_pos,
        RX_SOF     => mac_mfb_sof,
        RX_EOF     => mac_mfb_eof,
        RX_SRC_RDY => mac_mfb_src_rdy,
        RX_DST_RDY => mac_mfb_dst_rdy,

        MII_TXD    => MII_TXD,
        MII_TXC    => MII_TXC,
        MII_VLD    => MII_VLD,
        MII_RDY    => MII_RDY
    );

end architecture;
