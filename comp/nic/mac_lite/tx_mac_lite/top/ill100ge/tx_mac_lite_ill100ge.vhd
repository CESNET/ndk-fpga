-- tx_mac_lite_ill100ge.vhd: TX MAC Lite top level module for Intel LL100GE IP
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_ILL100GE is
    generic(
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        MFB_REGIONS     : natural := 1; -- must be 1
        MFB_REGION_SIZE : natural := 8; -- must be power of two, only 8 is tested
        MFB_BLOCK_SIZE  : natural := 8; -- must be 8
        MFB_ITEM_WIDTH  : natural := 8; -- must be 8
        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================
        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
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
        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- OUTPUT AVALON-ST INTERFACE (to Intel LL100GE IP)
        -- =====================================================================
        TX_CLK         : in  std_logic;
        TX_RESET       : in  std_logic;
        TX_AVST_DATA   : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_AVST_SOP    : out std_logic;
        TX_AVST_EOP    : out std_logic;
        TX_AVST_EMPTY  : out std_logic_vector(log2(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        TX_AVST_ERROR  : out std_logic;
        TX_AVST_VALID  : out std_logic;
        TX_AVST_READY  : in  std_logic;

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE (TX_CLK)
        -- =====================================================================
        -- Active during frame transmission
        OUTGOING_FRAME : out std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ILL100GE is

    constant DATA_WIDTH : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant FIFO_DEPTH : natural := 512;

    signal mac_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mac_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal mac_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal mac_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mac_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mac_mfb_src_rdy : std_logic;
    signal mac_mfb_dst_rdy : std_logic;

begin

    tx_mac_lite_i : entity work.TX_MAC_LITE
    generic map(
        TX_REGIONS      => MFB_REGIONS,
        TX_REGION_SIZE  => MFB_REGION_SIZE,
        TX_BLOCK_SIZE   => MFB_BLOCK_SIZE,
        TX_ITEM_WIDTH   => MFB_ITEM_WIDTH,
        PKT_MTU_BYTES   => PKT_MTU_BYTES,
        RX_INCLUDE_CRC  => false,
        RX_INCLUDE_IPG  => false,
        CRC_INSERT_EN   => false,
        IPG_GENERATE_EN => false,
        USE_DSP_CNT     => USE_DSP_CNT,
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

        TX_CLK         => TX_CLK,
        TX_RESET       => TX_RESET,
        TX_MFB_DATA    => mac_mfb_data,
        TX_MFB_SOF_POS => mac_mfb_sof_pos,
        TX_MFB_EOF_POS => mac_mfb_eof_pos,
        TX_MFB_SOF     => mac_mfb_sof,
        TX_MFB_EOF     => mac_mfb_eof,
        TX_MFB_SRC_RDY => mac_mfb_src_rdy,
        TX_MFB_DST_RDY => mac_mfb_dst_rdy,

        OUTGOING_FRAME => OUTGOING_FRAME
    );

    adapter_avst_100g_i : entity work.TX_MAC_LITE_ADAPTER_AVST_100G
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        FIFO_DEPTH => FIFO_DEPTH,
        DEVICE     => DEVICE
    )
    port map (
        CLK            => TX_CLK,
        RESET          => TX_RESET,

        RX_MFB_DATA    => mac_mfb_data,
        RX_MFB_SOF_POS => mac_mfb_sof_pos,
        RX_MFB_EOF_POS => mac_mfb_eof_pos,
        RX_MFB_SOF     => mac_mfb_sof,
        RX_MFB_EOF     => mac_mfb_eof,
        RX_MFB_SRC_RDY => mac_mfb_src_rdy,
        RX_MFB_DST_RDY => mac_mfb_dst_rdy,

        TX_AVST_DATA   => TX_AVST_DATA,
        TX_AVST_SOP    => TX_AVST_SOP,
        TX_AVST_EOP    => TX_AVST_EOP,
        TX_AVST_EMPTY  => TX_AVST_EMPTY,
        TX_AVST_ERROR  => TX_AVST_ERROR,
        TX_AVST_VALID  => TX_AVST_VALID,
        TX_AVST_READY  => TX_AVST_READY
    );

end architecture;
