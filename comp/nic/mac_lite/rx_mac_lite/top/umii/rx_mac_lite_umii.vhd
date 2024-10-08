-- rx_mac_lite_umii.vhd: Top module of RX MAC LITE with Universal MII decoder
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

entity RX_MAC_LITE_UMII is
    generic(
        -- =====================================================================
        -- MII CONFIGURATION:
        -- =====================================================================
        -- Data width of MII data signal, must be power of two, minimum is 64
        MII_DW           : natural := 2048;
        -- Length of link error timeout counter (number of counter bits)
        CNT_ERROR_LENGTH : natural := 5;
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        -- By default the RX parameters are calculated automatically from MII_DW.
        -- Useful for enlargement data width from 128b (MII) to 512b (TX).
        TX_REGIONS       : natural := max(MII_DW/512,1);
        -- SOF must be aligned by 8 bytes
        TX_BLOCK_SIZE    : natural := 8;
        -- one item = one byte
        TX_ITEM_WIDTH    : natural := 8;
        TX_REGION_SIZE   : natural := (MII_DW/TX_REGIONS)/(TX_BLOCK_SIZE*TX_ITEM_WIDTH);
        -- If true, the MFB bus doubles data width (number of regions) before
        -- the packet buffer (on RX_CLK). RESIZE_BUFFER feature is allowed only
        -- when the MFB bus increases (TX MFB width >= 2x MII_DW width)!
        RESIZE_BUFFER    : boolean := false;
        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================
        -- ID of this network port, it is inserted into the packet metadata.
        NETWORK_PORT_ID : natural := 0;
        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Enable of CRC checking, when is disable, resources are ~60% lower.
        CRC_CHECK_EN    : boolean := true;
        -- Enable of CRC removing.
        CRC_REMOVE_EN   : boolean := true;
        -- Enable of MAC checking.
        MAC_CHECK_EN    : boolean := true;
        -- Number of maximum MAC address in CAM memory, maximum value is 16.
        MAC_COUNT       : natural := 4;
        -- Enable of timestamping frames.
        TIMESTAMP_EN    : boolean := true;
        -- Select correct FPGA device.
        -- ULTRASCALE,...
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
        -- INPUT MII INTERFACE (XGMII, XLGMII, CGMII, CDMII,...) (RX_CLK)
        -- =====================================================================
        -- MII signal with data bits
        MII_RXD        : in  std_logic_vector(MII_DW-1 downto 0);
        -- MII signal with control flags
        MII_RXC        : in  std_logic_vector(MII_DW/8-1 downto 0);
        -- Valid signal of MII word, set to VCC if this signal is not needed.
        MII_VLD        : in  std_logic;

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
        TX_MFB_DATA     : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic;

        -- TX MVB METADATA INTERFACE
        -- ---------------------------------------------------------------------
        -- Metadata MVB bus is valid for each transmitted frame (EOF) from this
        -- module. Description of DATA bits are in eth_hdr_pack package.
        TX_MVB_DATA     : out std_logic_vector(TX_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(TX_REGIONS-1 downto 0);
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

architecture FULL of RX_MAC_LITE_UMII is

    -- The RX MFB parameters are calculated automatically from MII configuration
    constant RX_REGIONS     : natural := max(MII_DW/512,1);
    constant RX_BLOCK_SIZE  : natural := 8;
    constant RX_ITEM_WIDTH  : natural := 8;
    constant RX_REGION_SIZE : natural := (MII_DW/RX_REGIONS)/(RX_BLOCK_SIZE*RX_ITEM_WIDTH);

    signal adp_mfb_data    : std_logic_vector(RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
    signal adp_mfb_sof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
    signal adp_mfb_eof_pos : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    signal adp_mfb_sof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal adp_mfb_eof     : std_logic_vector(RX_REGIONS-1 downto 0);
    signal adp_mfb_error   : std_logic_vector(RX_REGIONS-1 downto 0);
    signal adp_mfb_src_rdy : std_logic;
    signal adp_link_up     : std_logic;

begin

    umii_dec_i : entity work.UMII_DEC
    generic map(
        MII_DW           => MII_DW,
        CNT_ERROR_LENGTH => CNT_ERROR_LENGTH,
        REGIONS          => RX_REGIONS,
        REGION_SIZE      => RX_REGION_SIZE,
        BLOCK_SIZE       => RX_BLOCK_SIZE,
        ITEM_WIDTH       => RX_ITEM_WIDTH
    )
    port map(
        CLK            => RX_CLK,
        RESET          => RX_RESET,

        MII_RXD        => MII_RXD,
        MII_RXC        => MII_RXC,
        MII_VLD        => MII_VLD,

        TX_DATA        => adp_mfb_data,
        TX_SOF_POS     => adp_mfb_sof_pos,
        TX_EOF_POS     => adp_mfb_eof_pos,
        TX_SOF         => adp_mfb_sof,
        TX_EOF         => adp_mfb_eof,
        TX_ERR         => adp_mfb_error,
        TX_SRC_RDY     => adp_mfb_src_rdy,

        LINK_UP        => adp_link_up,
        INCOMING_FRAME => INCOMING_FRAME
    );

    rx_mac_lite_i : entity work.RX_MAC_LITE
    generic map(
        RX_REGIONS      => RX_REGIONS,
        RX_REGION_SIZE  => RX_REGION_SIZE,
        RX_BLOCK_SIZE   => RX_BLOCK_SIZE,
        RX_ITEM_WIDTH   => RX_ITEM_WIDTH,
        TX_REGIONS      => TX_REGIONS,
        TX_REGION_SIZE  => TX_REGION_SIZE,
        TX_BLOCK_SIZE   => TX_BLOCK_SIZE,
        TX_ITEM_WIDTH   => TX_ITEM_WIDTH,
        RESIZE_BUFFER   => RESIZE_BUFFER,
        NETWORK_PORT_ID => NETWORK_PORT_ID,
        PKT_MTU_BYTES   => PKT_MTU_BYTES,
        CRC_IS_RECEIVED => True,
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
        RX_MFB_SOF_POS  => adp_mfb_sof_pos,
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
        INCOMING_FRAME  => open,

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
