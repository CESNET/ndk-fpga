-- tx_mac_lite_cmac.vhd: TX MAC Lite top level module for Xilinx CMAC IP
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_CMAC is
    generic(
        -- =====================================================================
        -- MFB CONFIGURATION (read only values):
        -- =====================================================================

        MFB_REGIONS     : natural := 1; -- must be 1
        MFB_REGION_SIZE : natural := 8; -- must be 8
        MFB_BLOCK_SIZE  : natural := 8; -- must be 8
        MFB_ITEM_WIDTH  : natural := 8; -- must be 8
        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================

        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Set true when input (RX MFB) packets contain CRC field.
        RX_INCLUDE_CRC  : boolean := False;
        -- Set true when you need use counters implemented in DSP.
        USE_DSP_CNT     : boolean := False;
        -- Select correct FPGA device.
        -- only ULTRASCALE is supported
        DEVICE          : string := "ULTRASCALE"
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
        --  INPUT MFB INTERFACE
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
        -- OUTPUT MFB INTERFACE (must be MFB(1,4,16,8), to CMAC Wrapper)
        -- =====================================================================
        TX_CLK         : in  std_logic;
        TX_RESET       : in  std_logic;
        TX_MFB_DATA    : out std_logic_vector(512-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(2-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(6-1 downto 0);
        TX_MFB_SOF     : out std_logic;
        TX_MFB_EOF     : out std_logic;
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic;

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE (TX_CLK)
        -- =====================================================================
        -- Active during frame transmission
        OUTGOING_FRAME : out std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_CMAC is

    signal mac_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mac_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal mac_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal mac_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mac_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mac_mfb_src_rdy : std_logic;
    signal mac_mfb_dst_rdy : std_logic;

    signal rbas_mfb_data    : std_logic_vector(512-1 downto 0);
    signal rbas_mfb_sof_pos : std_logic_vector(2-1 downto 0);
    signal rbas_mfb_eof_pos : std_logic_vector(6-1 downto 0);
    signal rbas_mfb_sof     : std_logic;
    signal rbas_mfb_eof     : std_logic;
    signal rbas_mfb_src_rdy : std_logic;
    signal rbas_mfb_dst_rdy : std_logic;

begin

    tx_mac_lite_i : entity work.TX_MAC_LITE
    generic map(
        TX_REGIONS      => MFB_REGIONS,
        TX_REGION_SIZE  => MFB_REGION_SIZE,
        TX_BLOCK_SIZE   => MFB_BLOCK_SIZE,
        TX_ITEM_WIDTH   => MFB_ITEM_WIDTH,
        PKT_MTU_BYTES   => PKT_MTU_BYTES,
        RX_INCLUDE_CRC  => RX_INCLUDE_CRC,
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

    -- conversion to MFB(1,4,16,8)
    rebase_i : entity work.CMAC_OBUF_REBASE
    port map(
       -- CLOCK AND RESET
       CMAC_CLK   => TX_CLK,
       CMAC_RESET => TX_RESET,

       RX_DATA    => mac_mfb_data,
       RX_SOP_POS => mac_mfb_sof_pos,
       RX_EOP_POS => mac_mfb_eof_pos,
       RX_SOP     => mac_mfb_sof(0),
       RX_EOP     => mac_mfb_eof(0),
       RX_SRC_RDY => mac_mfb_src_rdy,
       RX_DST_RDY => mac_mfb_dst_rdy,

       TX_DATA    => rbas_mfb_data,
       TX_SOF_POS => rbas_mfb_sof_pos,
       TX_EOF_POS => rbas_mfb_eof_pos,
       TX_SOF     => rbas_mfb_sof,
       TX_EOF     => rbas_mfb_eof,
       TX_SRC_RDY => rbas_mfb_src_rdy,
       TX_DST_RDY => rbas_mfb_dst_rdy
    );

    -- SOF of every first packet in word must be at first byte
    corrector_i : entity work.CMAC_OBUF_REBASE_CORRECTOR
    port map(
       CMAC_CLK   => TX_CLK,
       CMAC_RESET => TX_RESET,

       RX_DATA    => rbas_mfb_data,
       RX_SOF_POS => rbas_mfb_sof_pos,
       RX_EOF_POS => rbas_mfb_eof_pos,
       RX_SOF     => rbas_mfb_sof,
       RX_EOF     => rbas_mfb_eof,
       RX_SRC_RDY => rbas_mfb_src_rdy,
       RX_DST_RDY => rbas_mfb_dst_rdy,

       TX_DATA    => TX_MFB_DATA,
       TX_SOF_POS => TX_MFB_SOF_POS,
       TX_EOF_POS => TX_MFB_EOF_POS,
       TX_SOF     => TX_MFB_SOF,
       TX_EOF     => TX_MFB_EOF,
       TX_SRC_RDY => TX_MFB_SRC_RDY,
       TX_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
