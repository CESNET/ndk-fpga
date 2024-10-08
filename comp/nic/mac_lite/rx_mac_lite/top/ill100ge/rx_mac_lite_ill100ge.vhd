-- rx_mac_lite_ill100ge.vhd: Top module of RX MAC LITE for Intel LL 100GE IP
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

entity RX_MAC_LITE_ILL100GE is
    generic(
        -- =====================================================================
        -- MFB CONFIGURATION (read only values):
        -- =====================================================================
        -- must be 1
        REGIONS         : natural := 1;
        -- must be 8
        REGION_SIZE     : natural := 8;
        -- must be 8
        BLOCK_SIZE      : natural := 8;
        -- must be 8
        ITEM_WIDTH      : natural := 8;

        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================
        -- ID of this network port, it is inserted into the packet metadata.
        NETWORK_PORT_ID : natural := 0;
        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Set true when CRC is part of frames in RX MFB bus.
        CRC_IS_RECEIVED : boolean := false;
        -- Enable of CRC checking, CRC_IS_RECEIVED must be true.
        -- When is disable, resources are ~60% lower.
        CRC_CHECK_EN    : boolean := false;
        -- Enable of CRC removing, CRC_IS_RECEIVED must be true.
        CRC_REMOVE_EN   : boolean := false;
        -- Enable of MAC checking.
        MAC_CHECK_EN    : boolean := true;
        -- Number of maximum MAC address in CAM memory, maximum value is 16.
        MAC_COUNT       : natural := 4;
        -- Enable of timestamping frames.
        TIMESTAMP_EN    : boolean := true;
        -- Select correct FPGA device.
        -- ULTRASCALE
        DEVICE          : string := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        RX_CLK          : in  std_logic;
        RX_RESET        : in  std_logic;
        TX_CLK          : in  std_logic;
        TX_RESET        : in  std_logic;

        -- =====================================================================
        -- RX INTERFACES (RX_CLK)
        -- =====================================================================

        -- RX AVST DATA INTERFACE
        -- ---------------------------------------------------------------------
        RX_AVST_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_AVST_SOP     : in  std_logic;
        RX_AVST_EOP     : in  std_logic;
        RX_AVST_EMPTY   : in  std_logic_vector(log2(REGIONS*REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_AVST_ERROR   : in  std_logic_vector(6-1 downto 0);
        RX_AVST_VALID   : in  std_logic;

        -- RX OTHERS SIGNALS
        -- ---------------------------------------------------------------------
        RX_PCS_READY    : in  std_logic;
        RX_BLOCK_LOCK   : in  std_logic;
        RX_AM_LOCK      : in  std_logic;

        -- =====================================================================
        -- INPUT TIMESTAMP INTERFACE (FROM TSU) (RX_CLK)
        -- =====================================================================
        -- Timestamp in nanosecond (new) format, more info in TSU.
        TSU_TS_NS       : in  std_logic_vector(64-1 downto 0);
        -- Valid flag of timestamp.
        TSU_TS_DV       : in  std_logic;

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE (RX_CLK)
        -- =====================================================================
        -- Active when link is up
        LINK_UP         : out std_logic;
        -- Active while receiving a frame
        INCOMING_FRAME  : out std_logic;

        -- =====================================================================
        -- TX INTERFACES (TX_CLK)
        -- =====================================================================

        -- TX MFB DATA INTERFACE
        -- ---------------------------------------------------------------------
        TX_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic;

        -- TX MVB METADATA INTERFACE
        -- ---------------------------------------------------------------------
        -- Metadata MVB bus is valid for each transmitted frame (EOF) from this
        -- module. Description of DATA bits are in eth_hdr_pack package.
        TX_MVB_DATA     : out std_logic_vector(REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(REGIONS-1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic;

        -- =====================================================================
        -- MI32 INTERFACE (MI_CLK)
        -- =====================================================================
        MI_CLK          : in  std_logic;
        MI_RESET        : in  std_logic;
        MI_DWR          : in  std_logic_vector(32-1 downto 0);
        MI_ADDR         : in  std_logic_vector(32-1 downto 0);
        MI_RD           : in  std_logic;
        MI_WR           : in  std_logic;
        MI_BE           : in  std_logic_vector(4-1 downto 0);
        MI_DRD          : out std_logic_vector(32-1 downto 0);
        MI_ARDY         : out std_logic;
        MI_DRDY         : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE_ILL100GE is

    signal adp_mfb_data    : std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal adp_mfb_sof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    signal adp_mfb_eof_pos : std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    signal adp_mfb_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal adp_mfb_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal adp_mfb_error   : std_logic_vector(REGIONS-1 downto 0);
    signal adp_mfb_src_rdy : std_logic;
    signal adp_link_up     : std_logic;

begin

    -- avst simple module support only readyLatency=0
    avst_simple_i : entity work.RX_MAC_LITE_ADAPTER_AVST_SIMPLE
    generic map(
        DATA_WIDTH => REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH
    )
    port map(
        CLK              => RX_CLK,
        RESET            => RX_RESET,

        IN_AVST_DATA     => RX_AVST_DATA,
        IN_AVST_SOP      => RX_AVST_SOP,
        IN_AVST_EOP      => RX_AVST_EOP,
        IN_AVST_EMPTY    => RX_AVST_EMPTY,
        IN_AVST_ERROR    => RX_AVST_ERROR,
        IN_AVST_VALID    => RX_AVST_VALID,
        IN_RX_PCS_READY  => RX_PCS_READY,
        IN_RX_BLOCK_LOCK => RX_BLOCK_LOCK,
        IN_RX_AM_LOCK    => RX_AM_LOCK,

        OUT_MFB_DATA     => adp_mfb_data,
        OUT_MFB_EOF_POS  => adp_mfb_eof_pos,
        OUT_MFB_SOF      => adp_mfb_sof,
        OUT_MFB_EOF      => adp_mfb_eof,
        OUT_MFB_ERROR    => adp_mfb_error,
        OUT_MFB_SRC_RDY  => adp_mfb_src_rdy,
        OUT_LINK_UP      => adp_link_up
    );

    rx_mac_lite_i : entity work.RX_MAC_LITE
    generic map(
        RX_REGIONS      => REGIONS,
        RX_REGION_SIZE  => REGION_SIZE,
        RX_BLOCK_SIZE   => BLOCK_SIZE,
        RX_ITEM_WIDTH   => ITEM_WIDTH,
        NETWORK_PORT_ID => NETWORK_PORT_ID,
        PKT_MTU_BYTES   => PKT_MTU_BYTES,
        CRC_IS_RECEIVED => CRC_IS_RECEIVED,
        CRC_CHECK_EN    => CRC_CHECK_EN,
        CRC_REMOVE_EN   => CRC_REMOVE_EN,
        MAC_CHECK_EN    => MAC_CHECK_EN,
        MAC_COUNT       => MAC_COUNT,
        TIMESTAMP_EN    => TIMESTAMP_EN,
        DEVICE          => DEVICE
    )
    port map(
        RX_CLK          => RX_CLK,
        RX_RESET        => RX_RESET,
        TX_CLK          => TX_CLK,
        TX_RESET        => TX_RESET,

        RX_MFB_DATA     => adp_mfb_data,
        RX_MFB_SOF_POS  => (others => '0'),
        RX_MFB_EOF_POS  => adp_mfb_eof_pos,
        RX_MFB_SOF      => adp_mfb_sof,
        RX_MFB_EOF      => adp_mfb_eof,
        RX_MFB_ERROR    => adp_mfb_error,
        RX_MFB_SRC_RDY  => adp_mfb_src_rdy,

        ADAPTER_LINK_UP => adp_link_up,

        TSU_TS_NS       => TSU_TS_NS,
        TSU_TS_DV       => TSU_TS_DV,

        TX_MFB_DATA     => TX_MFB_DATA,
        TX_MFB_SOF_POS  => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS  => TX_MFB_EOF_POS,
        TX_MFB_SOF      => TX_MFB_SOF,
        TX_MFB_EOF      => TX_MFB_EOF,
        TX_MFB_SRC_RDY  => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY  => TX_MFB_DST_RDY,
        TX_MVB_DATA     => TX_MVB_DATA,
        TX_MVB_VLD      => TX_MVB_VLD,
        TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

        LINK_UP         => LINK_UP,
        INCOMING_FRAME  => INCOMING_FRAME,

        MI_CLK          => MI_CLK,
        MI_RESET        => MI_RESET,
        MI_DWR          => MI_DWR,
        MI_ADDR         => MI_ADDR,
        MI_RD           => MI_RD,
        MI_WR           => MI_WR,
        MI_BE           => MI_BE,
        MI_DRD          => MI_DRD,
        MI_ARDY         => MI_ARDY,
        MI_DRDY         => MI_DRDY
    );

end architecture;
