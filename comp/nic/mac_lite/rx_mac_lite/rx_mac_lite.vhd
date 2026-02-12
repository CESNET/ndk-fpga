-- rx_mac_lite.vhd: Base module of RX MAC LITE
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

entity RX_MAC_LITE is
    generic (
        -- =====================================================================
        -- MFB CONFIGURATION:
        --
        -- RX MFB configuration, allows you to set the required data width
        -- according to the selected Ethernet standard.
        -- =====================================================================

        -- RX MFB: number of regions in word, must be power of 2
        RX_REGIONS      : natural := 4;
        -- RX MFB: number of blocks in region, must be power of 2
        RX_REGION_SIZE  : natural := 8;
        -- RX MFB: number of items in block, must be >= 4 and power of 2
        RX_BLOCK_SIZE   : natural := 8;
        -- RX MFB: width of one item in bits, must be 8
        RX_ITEM_WIDTH   : natural := 8;

        -- =====================================================================
        -- TX MFB configuration, by default the same as RX. Useful, for example,
        --
        -- for enlargement data width from 128b (RX) to 512b (TX).
        -- =====================================================================

        -- TX MFB: number of regions in word, by default same as RX
        TX_REGIONS      : natural := RX_REGIONS;
        -- TX MFB: number of blocks in region, by default same as RX
        TX_REGION_SIZE  : natural := RX_REGION_SIZE;
        -- TX MFB: number of items in block, by default same as RX
        TX_BLOCK_SIZE   : natural := RX_BLOCK_SIZE;
        -- TX MFB: width of one item in bits, by default same as RX
        TX_ITEM_WIDTH   : natural := RX_ITEM_WIDTH;

        -- If true, the MFB bus resize data width before the packet buffer (on
        -- RX_CLK). See also RESIZE_FULL for additional settings.
        RESIZE_BUFFER   : boolean := false;
        -- This parameter is active only if RESIZE_BUFFER=True. If is set to True,
        -- the bus before the buffer will be resized directly to the TX parameters,
        -- otherwise only the number of regions will be doubled to 2*RX_REGIONS.
        -- If True, packets smaller than 60B must not be sent to the RX input.
        RESIZE_FULL     : boolean := false;

        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================

        -- ID of this network port, it is inserted into the packet metadata.
        NETWORK_PORT_ID : natural := 0;
        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Set true when CRC is part of frames in RX MFB bus.
        CRC_IS_RECEIVED : boolean := true;
        -- Enable of CRC checking, CRC_IS_RECEIVED must be true.
        -- When is disable, resources are ~60% lower.
        CRC_CHECK_EN    : boolean := true;
        -- Enable of CRC removing, CRC_IS_RECEIVED must be true.
        CRC_REMOVE_EN   : boolean := true;
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
    port (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================

        -- Clock for RX MFB interface
        RX_CLK          : in  std_logic;
        -- Reset synchronized with RX_CLK
        RX_RESET        : in  std_logic;
        -- Clock for TX MFB interface
        TX_CLK          : in  std_logic;
        -- Reset synchronized with TX_CLK
        TX_RESET        : in  std_logic;

        -- =====================================================================
        -- RX MAC LITE ADAPTER INTERFACES
        --
        -- =====================================================================

        -- RX MFB DATA INTERFACE (Don't support gaps inside frame!)
        -- ---------------------------------------------------------------------

        -- RX MFB: data word with frames (packets)
        RX_MFB_DATA     : in  std_logic_vector(RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        -- RX MFB: Start Of Frame (SOF) flag for each MFB region
        RX_MFB_SOF_POS  : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
        -- RX MFB: End Of Frame (EOF) flag for each MFB region
        RX_MFB_EOF_POS  : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        -- RX MFB: SOF position for each MFB region in MFB blocks
        RX_MFB_SOF      : in  std_logic_vector(RX_REGIONS-1 downto 0);
        -- RX MFB: EOF position for each MFB region in MFB items
        RX_MFB_EOF      : in  std_logic_vector(RX_REGIONS-1 downto 0);
        -- RX MFB: MII Error flag for each MFB region, valid with EOF
        RX_MFB_MII_ERR  : in  std_logic_vector(RX_REGIONS-1 downto 0) := (others => '0');
        -- RX MFB: CRC Error flag for each MFB region, valid with EOF
        RX_MFB_CRC_ERR  : in  std_logic_vector(RX_REGIONS-1 downto 0) := (others => '0');
        -- RX MFB: source ready of each MFB bus, don't support gaps inside frame!
        RX_MFB_SRC_RDY  : in  std_logic;

        -- =====================================================================
        -- RX STATUS INTERFACE
        -- =====================================================================

        -- Link Up flag input, active when link is up
        ADAPTER_LINK_UP : in  std_logic;

        -- =====================================================================
        -- INPUT TIMESTAMP INTERFACE (FROM TSU)
        -- =====================================================================

        -- Timestamp in nanosecond (new) format, more info in TSU.
        TSU_TS_NS       : in  std_logic_vector(64-1 downto 0);
        -- Valid flag of timestamp.
        TSU_TS_DV       : in  std_logic;

        -- =====================================================================
        -- TX INTERFACES
        -- =====================================================================

        -- TX MFB DATA INTERFACE
        -- ---------------------------------------------------------------------

        -- TX MFB: data word with frames (packets)
        TX_MFB_DATA     : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
        -- TX MFB: Start Of Frame (SOF) flag for each MFB region
        TX_MFB_SOF_POS  : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
        -- TX MFB: End Of Frame (EOF) flag for each MFB region
        TX_MFB_EOF_POS  : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
        -- TX MFB: SOF position for each MFB region in MFB blocks
        TX_MFB_SOF      : out std_logic_vector(TX_REGIONS-1 downto 0);
        -- TX MFB: EOF position for each MFB region in MFB items
        TX_MFB_EOF      : out std_logic_vector(TX_REGIONS-1 downto 0);
        -- TX MFB: source ready of each MFB bus
        TX_MFB_SRC_RDY  : out std_logic;
        -- TX MFB: destination ready of each MFB bus
        TX_MFB_DST_RDY  : in  std_logic;

        -- =====================================================================
        -- TX MVB METADATA INTERFACE
        --
        -- Metadata MVB bus is valid for each transmitted frame (EOF) from this
        -- module. Description of DATA bits are in eth_hdr_pack package.
        -- =====================================================================

        -- TX MVB: data word with MVB items. Description of DATA bits are in eth_hdr_pack package.
        TX_MVB_DATA     : out std_logic_vector(TX_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item. There is one item for each packet on the TX MFB.
        TX_MVB_VLD      : out std_logic_vector(TX_REGIONS-1 downto 0);
        -- TX MVB: source ready of each MVB bus
        TX_MVB_SRC_RDY  : out std_logic;
        -- TX MVB: destination ready of each MVB bus
        TX_MVB_DST_RDY  : in  std_logic;

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE
        -- =====================================================================

        -- Active when link is up
        LINK_UP         : out std_logic;
        -- Active while receiving a frame
        INCOMING_FRAME  : out std_logic;

        -- =====================================================================
        -- MI32 INTERFACE
        -- =====================================================================

        -- Clock for MI bus
        MI_CLK          : in  std_logic;
        -- Reset synchronized with MI_CLK
        MI_RESET        : in  std_logic;
        -- MI bus: data from master to slave (write data)
        MI_DWR          : in  std_logic_vector(32-1 downto 0);
        -- MI bus: slave address
        MI_ADDR         : in  std_logic_vector(32-1 downto 0);
        -- MI bus: byte enable
        MI_RD           : in  std_logic;
        -- MI bus: read request
        MI_WR           : in  std_logic;
        -- MI bus: write request
        MI_BE           : in  std_logic_vector(4-1 downto 0);
        -- MI bus: ready of slave module
        MI_DRD          : out std_logic_vector(32-1 downto 0);
        -- MI bus: data from slave to master (read data)
        MI_ARDY         : out std_logic;
        -- MI bus: valid of MI_DRD data signal
        MI_DRDY         : out std_logic
    );
end entity;

architecture FULL of RX_MAC_LITE is

    -- =====================================================================
    -- MFB configuration for packet buffer and next modules
    -- =====================================================================

    -- select resize values to 2x regions or to TX parameters
    constant RS_REGIONS               : natural := tsel(RESIZE_FULL, TX_REGIONS, 2*RX_REGIONS);
    constant RS_REGION_SIZE           : natural := tsel(RESIZE_FULL, TX_REGION_SIZE, RX_REGION_SIZE);
    constant RS_BLOCK_SIZE            : natural := tsel(RESIZE_FULL, TX_BLOCK_SIZE, RX_BLOCK_SIZE);
    constant RS_ITEM_WIDTH            : natural := tsel(RESIZE_FULL, TX_ITEM_WIDTH, RX_ITEM_WIDTH);
    -- enable resize before buffer
    constant BF_REGIONS               : natural := tsel(RESIZE_BUFFER, RS_REGIONS, RX_REGIONS);
    constant BF_REGION_SIZE           : natural := tsel(RESIZE_BUFFER, RS_REGION_SIZE, RX_REGION_SIZE);
    constant BF_BLOCK_SIZE            : natural := tsel(RESIZE_BUFFER, RS_BLOCK_SIZE, RX_BLOCK_SIZE);
    constant BF_ITEM_WIDTH            : natural := tsel(RESIZE_BUFFER, RS_ITEM_WIDTH, RX_ITEM_WIDTH);

    -- =====================================================================
    -- Helper MFB constants
    -- =====================================================================

    constant BF_DATA_W                : natural := BF_REGIONS*BF_REGION_SIZE*BF_BLOCK_SIZE*BF_ITEM_WIDTH;
    constant RX_DATA_W                : natural := RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH;
    constant RX_SOF_POS_W             : natural := RX_REGIONS*max(1,log2(RX_REGION_SIZE));
    constant RX_EOF_POS_W             : natural := RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE));

    -- =====================================================================
    -- Others constants
    -- =====================================================================

    constant DFIFO_ITEMS_MIN          : natural := 2**log2(div_roundup((PKT_MTU_BYTES+1),(BF_DATA_W/8)));
    constant DFIFO_ITEMS              : natural := max(DFIFO_ITEMS_MIN,512);
    constant MFIFO_ITEMS              : natural := (DFIFO_ITEMS*BF_DATA_W)/512;
    constant LEN_WIDTH                : natural := 16;
    constant MAC_STATUS_WIDTH         : natural := log2(MAC_COUNT)+4;
    constant FLC_SYNC_WIDTH           : natural := 1+RX_EOF_POS_W+RX_SOF_POS_W+RX_DATA_W+(LEN_WIDTH+6)*RX_REGIONS;
    constant INBANDCRC                : boolean := CRC_IS_RECEIVED and not CRC_REMOVE_EN;
    constant SM_CNT_TICKS_WIDTH       : natural := 24;
    constant SM_CNT_BYTES_WIDTH       : natural := 32;

    signal s_rx_inc_frame             : std_logic_vector(RX_REGIONS downto 0);
    signal s_rx_mfb_error             : std_logic_vector(RX_REGIONS*2-1 downto 0);

    signal s_in_data                  : std_logic_vector(RX_DATA_W-1 downto 0);
    signal s_in_sof_pos               : std_logic_vector(RX_SOF_POS_W-1 downto 0);
    signal s_in_eof_pos               : std_logic_vector(RX_EOF_POS_W-1 downto 0);
    signal s_in_sof                   : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_in_eof                   : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_in_error                 : std_logic_vector(RX_REGIONS*2-1 downto 0);
    signal s_in_src_rdy               : std_logic;

    signal s_cut_data                 : std_logic_vector(RX_DATA_W-1 downto 0);
    signal s_cut_sof_pos              : std_logic_vector(RX_SOF_POS_W-1 downto 0);
    signal s_cut_eof_pos              : std_logic_vector(RX_EOF_POS_W-1 downto 0);
    signal s_cut_sof                  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_cut_eof                  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_cut_adapter_err          : std_logic_vector(RX_REGIONS*2-1 downto 0);
    signal s_cut_adapter_err_arr      : slv_array_t(RX_REGIONS-1 downto 0)(2-1 downto 0);
    signal s_cut_src_rdy              : std_logic;
    signal s_cut_crc_cut_err          : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_cut_metadata             : std_logic_vector(RX_REGIONS*3-1 downto 0);

    signal s_flc_data                 : std_logic_vector(RX_DATA_W-1 downto 0);
    signal s_flc_sof_pos              : std_logic_vector(RX_SOF_POS_W-1 downto 0);
    signal s_flc_eof_pos              : std_logic_vector(RX_EOF_POS_W-1 downto 0);
    signal s_flc_sof                  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_eof                  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_src_rdy              : std_logic;
    signal s_flc_crc_err              : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_mii_err              : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_len_max_err          : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_len_min_err          : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_frame_len            : std_logic_vector(RX_REGIONS*LEN_WIDTH-1 downto 0);
    signal s_flc_crc_cut_err          : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_flc_metadata             : std_logic_vector(RX_REGIONS*3-1 downto 0);
    signal s_flc_len_min_err_fixed    : std_logic_vector(RX_REGIONS-1 downto 0);

    signal s_flc_sync_in              : std_logic_vector(FLC_SYNC_WIDTH-1 downto 0);
    signal s_flc_sync_out             : std_logic_vector(FLC_SYNC_WIDTH-1 downto 0);

    signal s_mac_status               : std_logic_vector(RX_REGIONS*MAC_STATUS_WIDTH-1 downto 0);
    signal s_ts_data                  : std_logic_vector(RX_REGIONS*65-1 downto 0);

    signal s_sync_data                : std_logic_vector(RX_DATA_W-1 downto 0);
    signal s_sync_sof_pos             : std_logic_vector(RX_SOF_POS_W-1 downto 0);
    signal s_sync_eof_pos             : std_logic_vector(RX_EOF_POS_W-1 downto 0);
    signal s_sync_sof                 : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_eof                 : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_src_rdy             : std_logic;
    signal s_sync_dst_rdy_dbg         : std_logic;
    signal s_sync_mii_err             : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_len_max_err         : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_len_min_err         : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_frame_len_ser       : std_logic_vector(RX_REGIONS*LEN_WIDTH-1 downto 0);
    signal s_sync_frame_len           : slv_array_t(RX_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_sync_crc_err             : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_crc_check_err       : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_status          : std_logic_vector(RX_REGIONS*MAC_STATUS_WIDTH-1 downto 0);
    signal s_sync_mac_err             : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_bcast           : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_mcast           : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_hit_vld         : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_hit_addr        : slv_array_t(RX_REGIONS-1 downto 0)(log2(MAC_COUNT)-1 downto 0);
    signal s_sync_timestamp_ser       : std_logic_vector(RX_REGIONS*65-1 downto 0);
    signal s_sync_timestamp           : slv_array_t(RX_REGIONS-1 downto 0)(65-1 downto 0);
    signal s_sync_adapter_err_masked  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_crc_err_masked      : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_len_min_err_masked  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_len_max_err_masked  : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_mac_err_masked      : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_error               : std_logic_vector(RX_REGIONS-1 downto 0);
    signal s_sync_metadata            : slv_array_t(RX_REGIONS-1 downto 0)(ETH_RX_HDR_WIDTH-1 downto 0) := (others => (others => '0'));

    signal s_bfin_data                : std_logic_vector(BF_DATA_W-1 downto 0);
    signal s_bfin_metadata_ser        : std_logic_vector(BF_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal s_bfin_metadata            : slv_array_t(BF_REGIONS-1 downto 0)(ETH_RX_HDR_WIDTH-1 downto 0);
    signal s_bfin_metactrl            : std_logic_vector(6-1 downto 0);
    signal s_bfin_err_mask            : std_logic_vector(5-1 downto 0);
    signal s_bfin_adapter_err_masked  : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_crc_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_len_min_err_masked  : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_len_max_err_masked  : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_mac_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_sof_pos             : std_logic_vector(BF_REGIONS*max(1,log2(BF_REGION_SIZE))-1 downto 0);
    signal s_bfin_eof_pos             : std_logic_vector(BF_REGIONS*max(1,log2(BF_REGION_SIZE*BF_BLOCK_SIZE))-1 downto 0);
    signal s_bfin_sof                 : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_eof                 : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_error               : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_bfin_src_rdy             : std_logic;

    signal s_buf_mfb_data             : std_logic_vector(BF_REGIONS*BF_REGION_SIZE*BF_BLOCK_SIZE*BF_ITEM_WIDTH-1 downto 0);
    signal s_buf_mfb_sof_pos          : std_logic_vector(BF_REGIONS*max(1,log2(BF_REGION_SIZE))-1 downto 0);
    signal s_buf_mfb_eof_pos          : std_logic_vector(BF_REGIONS*max(1,log2(BF_REGION_SIZE*BF_BLOCK_SIZE))-1 downto 0);
    signal s_buf_mfb_sof              : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_buf_mfb_eof              : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_buf_mfb_src_rdy          : std_logic;
    signal s_buf_mfb_dst_rdy          : std_logic;

    signal s_buf_mvb_data             : std_logic_vector(BF_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal s_buf_mvb_vld              : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_buf_mvb_src_rdy          : std_logic;
    signal s_buf_mvb_dst_rdy          : std_logic;

    signal s_stin_valid               : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_discarded           : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_buffer_ovf          : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_mii_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_crc_err             : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_crc_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_len_min_err         : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_len_max_err         : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_len_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_mac_err             : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_mac_err_masked      : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_mac_bcast           : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_mac_mcast           : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_drop_off            : std_logic_vector(BF_REGIONS-1 downto 0);
    signal s_stin_frame_len           : slv_array_t(BF_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal s_stin_metadata            : slv_array_t(BF_REGIONS-1 downto 0)(ETH_RX_HDR_WIDTH-1 downto 0);
    signal s_stin_metactrl            : std_logic_vector(6-1 downto 0);
    signal s_stin_err_mask            : std_logic_vector(5-1 downto 0);
    signal s_stin_enable              : std_logic;
    signal s_buffer_status            : std_logic_vector(2-1 downto 0);

    signal s_stat_out_base_total      : std_logic_vector(63 downto 0);
    signal s_stat_out_base_passed     : std_logic_vector(63 downto 0);
    signal s_stat_out_base_dropped    : std_logic_vector(63 downto 0);
    signal s_stat_out_base_drop_off   : std_logic_vector(63 downto 0);
    signal s_stat_out_base_drop_ovf   : std_logic_vector(63 downto 0);
    signal s_stat_out_base_drop_flt   : std_logic_vector(63 downto 0);
    signal s_stat_out_base_drop_err   : std_logic_vector(63 downto 0);
    signal s_stat_out_base_err_len    : std_logic_vector(63 downto 0);
    signal s_stat_out_base_err_mii    : std_logic_vector(63 downto 0);
    signal s_stat_out_base_err_crc    : std_logic_vector(63 downto 0);
    signal s_stat_out_rx_bytes        : std_logic_vector(63 downto 0);
    signal s_stat_out_tx_bytes        : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_crc_err     : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_mac_err     : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_over_mtu    : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_below_min   : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_mac_bcast   : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_mac_mcast   : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_fragment    : std_logic_vector(63 downto 0);
    signal s_stat_out_rfc_jabber      : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_undersize  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_64         : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_65_127     : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_128_255    : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_256_511    : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_512_1023   : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_1024_1518  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_over_1518  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_1519_2047  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_2048_4095  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_4096_8191  : std_logic_vector(63 downto 0);
    signal s_stat_out_hist_over_8191  : std_logic_vector(63 downto 0);

    signal s_sm_cnt_ticks             : std_logic_vector(SM_CNT_TICKS_WIDTH-1 downto 0);
    signal s_sm_cnt_ticks_max         : std_logic;
    signal s_sm_cnt_bytes             : std_logic_vector(SM_CNT_BYTES_WIDTH-1 downto 0);
    signal s_sm_cnt_packets           : std_logic_vector(SM_CNT_BYTES_WIDTH-1 downto 0);
    signal s_sm_cnt_clear             : std_logic;

    signal s_ctl_enable               : std_logic;
    signal s_ctl_frame_len_max        : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_ctl_frame_len_min        : std_logic_vector(LEN_WIDTH-1 downto 0);
    signal s_ctl_mac_check_mode       : std_logic_vector(2-1 downto 0);
    signal s_ctl_error_mask           : std_logic_vector(5-1 downto 0);
    signal s_ctl_stat_sw_reset        : std_logic;
    signal s_ctl_stat_take_snapshot   : std_logic;
    signal s_ctl_stat_read_snapshot   : std_logic;

    signal s_cam_write_data           : std_logic_vector(49-1 downto 0);
    signal s_cam_write_addr           : std_logic_vector(log2(MAC_COUNT)-1 downto 0);
    signal s_cam_write_en             : std_logic;
    signal s_cam_write_rdy            : std_logic;

begin

    LINK_UP <= ADAPTER_LINK_UP;

    rx_mfb_error_g : for r in 0 to RX_REGIONS-1 generate
        s_rx_mfb_error(r*2+0) <= RX_MFB_CRC_ERR(r);
        s_rx_mfb_error(r*2+1) <= RX_MFB_MII_ERR(r);
    end generate;

    -- input register for better timing
    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            s_in_data        <= RX_MFB_DATA;
            s_in_sof_pos     <= RX_MFB_SOF_POS;
            s_in_eof_pos     <= RX_MFB_EOF_POS;
            s_in_sof         <= RX_MFB_SOF;
            s_in_eof         <= RX_MFB_EOF;
            s_in_error       <= s_rx_mfb_error;
            s_in_src_rdy     <= RX_MFB_SRC_RDY;
            if (RX_RESET = '1') then
                s_in_src_rdy <= '0';
            end if;
        end if;
    end process;

    process (all)
    begin
        for r in 0 to RX_REGIONS-1 loop
            s_rx_inc_frame(r+1) <= (s_in_sof(r) and not s_in_eof(r) and not s_rx_inc_frame(r)) or
                               (s_in_sof(r) and s_in_eof(r) and s_rx_inc_frame(r)) or
                               (not s_in_sof(r) and not s_in_eof(r) and s_rx_inc_frame(r));
        end loop;
    end process;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            if (RX_RESET = '1') then
                s_rx_inc_frame(0) <= '0';
            elsif (s_in_src_rdy = '1') then
                s_rx_inc_frame(0) <= s_rx_inc_frame(RX_REGIONS);
            end if;
        end if;
    end process;

    process (RX_CLK)
    begin
        if (rising_edge(RX_CLK)) then
            INCOMING_FRAME <= s_rx_inc_frame(0) or s_in_src_rdy;
        end if;
    end process;

    -- =========================================================================
    --  CRC CUTTER (latency = 2 cycles)
    -- =========================================================================

    crc_cutter_g : if (CRC_IS_RECEIVED and CRC_REMOVE_EN) generate
        crc_cutter_i : entity work.RX_MAC_LITE_CRC_CUTTER
        generic map (
            REGIONS     => RX_REGIONS,
            REGION_SIZE => RX_REGION_SIZE,
            BLOCK_SIZE  => RX_BLOCK_SIZE,
            ITEM_WIDTH  => RX_ITEM_WIDTH,
            META_WIDTH  => 2,
            OUTPUT_REG  => true
        )
        port map (
            CLK            => RX_CLK,
            RESET          => RX_RESET,

            RX_DATA        => s_in_data,
            RX_SOF_POS     => s_in_sof_pos,
            RX_EOF_POS     => s_in_eof_pos,
            RX_SOF         => s_in_sof,
            RX_EOF         => s_in_eof,
            RX_SRC_RDY     => s_in_src_rdy,
            RX_METADATA    => s_in_error,

            TX_DATA        => s_cut_data,
            TX_SOF_POS     => s_cut_sof_pos,
            TX_EOF_POS     => s_cut_eof_pos,
            TX_SOF         => s_cut_sof,
            TX_EOF         => s_cut_eof,
            TX_SRC_RDY     => s_cut_src_rdy,
            TX_METADATA    => s_cut_adapter_err,
            TX_CRC_CUT_ERR => s_cut_crc_cut_err
        );
    else generate
        s_cut_data        <= s_in_data;
        s_cut_sof_pos     <= s_in_sof_pos;
        s_cut_eof_pos     <= s_in_eof_pos;
        s_cut_sof         <= s_in_sof;
        s_cut_eof         <= s_in_eof;
        s_cut_src_rdy     <= s_in_src_rdy;
        s_cut_adapter_err <= s_in_error;
        s_cut_crc_cut_err <= (others => '0');
    end generate;

    s_cut_adapter_err_arr <= slv_array_deser(s_cut_adapter_err, RX_REGIONS, 2);

    cut_metadata_pack_g : for r in 0 to RX_REGIONS-1 generate
        s_cut_metadata(r*3+0) <= s_cut_adapter_err_arr(r)(0);
        s_cut_metadata(r*3+1) <= s_cut_adapter_err_arr(r)(1);
        s_cut_metadata(r*3+2) <= s_cut_crc_cut_err(r);
    end generate;

    -- =========================================================================
    --  CHECKING STAGE (latency = 9 cycles)
    -- =========================================================================

    -- -------------------------------------------------------------------------
    --  FRAME LENGHT CHECK MODULE
    -- -------------------------------------------------------------------------

    -- frame lenght check -- latency 4 cycles
    frame_lng_check_i : entity work.MFB_FRAME_LNG_CHECK
    generic map (
        REGIONS     => RX_REGIONS,
        REGION_SIZE => RX_REGION_SIZE,
        BLOCK_SIZE  => RX_BLOCK_SIZE,
        ITEM_WIDTH  => RX_ITEM_WIDTH,
        META_WIDTH  => 3,
        LNG_WIDTH   => LEN_WIDTH
    )
    port map (
        CLK            => RX_CLK,
        RESET          => RX_RESET,

        FRAME_LNG_MAX  => s_ctl_frame_len_max,
        FRAME_LNG_MIN  => s_ctl_frame_len_min,

        RX_DATA        => s_cut_data,
        RX_META        => s_cut_metadata,
        RX_SOF_POS     => s_cut_sof_pos,
        RX_EOF_POS     => s_cut_eof_pos,
        RX_SOF         => s_cut_sof,
        RX_EOF         => s_cut_eof,
        RX_SRC_RDY     => s_cut_src_rdy,
        RX_DST_RDY     => open,

        TX_DATA        => s_flc_data,
        TX_META        => s_flc_metadata,
        TX_SOF_POS     => s_flc_sof_pos,
        TX_EOF_POS     => s_flc_eof_pos,
        TX_SOF         => s_flc_sof,
        TX_EOF         => s_flc_eof,
        TX_SRC_RDY     => s_flc_src_rdy,
        TX_DST_RDY     => '1',

        TX_LNG_MAX_ERR => s_flc_len_max_err,
        TX_LNG_MIN_ERR => s_flc_len_min_err,
        TX_FRAME_LNG   => s_flc_frame_len
    );

    flc_metadata_unpack_g : for r in 0 to RX_REGIONS-1 generate
        s_flc_crc_err(r)     <= s_flc_metadata(r*3+0) or s_flc_metadata(r*3+2);
        s_flc_mii_err(r)     <= s_flc_metadata(r*3+1);
        s_flc_crc_cut_err(r) <= s_flc_metadata(r*3+2);
    end generate;

    s_flc_len_min_err_fixed <= s_flc_len_min_err or s_flc_crc_cut_err;

    s_flc_sync_in <= s_flc_src_rdy & s_flc_eof & s_flc_sof & s_flc_eof_pos &
                     s_flc_sof_pos & s_flc_data & s_flc_frame_len & s_flc_len_min_err_fixed &
                     s_flc_len_max_err & s_flc_mii_err & s_flc_crc_err;

    -- If RESET has 5 or more cycles, then it is enough SH_REG without reset.
    flc_sync_shreg_i : entity work.SH_REG_BASE_STATIC
    generic map (
        NUM_BITS   => 5,
        DATA_WIDTH => FLC_SYNC_WIDTH,
        DEVICE     => DEVICE
    )
    port map (
        CLK        => RX_CLK,
        DIN        => s_flc_sync_in,
        CE         => '1',
        DOUT       => s_flc_sync_out
    );

    s_sync_src_rdy       <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W+RX_REGIONS+RX_REGIONS);
    s_sync_eof           <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W+RX_REGIONS+RX_REGIONS-1 downto 4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W+RX_REGIONS);
    s_sync_sof           <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W+RX_REGIONS-1 downto 4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W);
    s_sync_eof_pos       <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W+RX_EOF_POS_W-1 downto 4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W);
    s_sync_sof_pos       <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W+RX_SOF_POS_W-1 downto 4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W);
    s_sync_data          <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH+RX_DATA_W-1 downto 4*RX_REGIONS+RX_REGIONS*LEN_WIDTH);
    s_sync_frame_len_ser <= s_flc_sync_out(4*RX_REGIONS+RX_REGIONS*LEN_WIDTH-1 downto 4*RX_REGIONS);
    s_sync_len_min_err   <= s_flc_sync_out(4*RX_REGIONS-1 downto 3*RX_REGIONS);
    s_sync_len_max_err   <= s_flc_sync_out(3*RX_REGIONS-1 downto 2*RX_REGIONS);
    s_sync_mii_err       <= s_flc_sync_out(2*RX_REGIONS-1 downto RX_REGIONS);
    s_sync_crc_err       <= s_flc_sync_out(RX_REGIONS-1 downto 0);

    s_sync_frame_len <= slv_array_downto_deser(s_sync_frame_len_ser,RX_REGIONS,LEN_WIDTH);

    -- -------------------------------------------------------------------------
    --  CRC CHECK MODULE
    -- -------------------------------------------------------------------------

    crc_check_en_g : if (CRC_IS_RECEIVED and CRC_CHECK_EN) generate
        -- check CRC -- latency 9 cycles
        crc_check_i : entity work.RX_MAC_LITE_CRC_CHECK
        generic map (
            REGIONS     => RX_REGIONS,
            REGION_SIZE => RX_REGION_SIZE,
            BLOCK_SIZE  => RX_BLOCK_SIZE,
            ITEM_WIDTH  => RX_ITEM_WIDTH,
            INBANDFCS   => INBANDCRC,
            DEVICE      => DEVICE
        )
        port map (
            -- CLOCK AND RESET
            CLK             => RX_CLK,
            RESET           => RX_RESET,
            -- RX MFB INTERFACE
            RX_DATA         => s_cut_data,
            RX_SOF_POS      => s_cut_sof_pos,
            RX_EOF_POS      => s_cut_eof_pos,
            RX_SOF          => s_cut_sof,
            RX_EOF          => s_cut_eof,
            RX_SRC_RDY      => s_cut_src_rdy,
            -- OUTPUT MVB CRC ERROR INTERFACE
            CRC_ERR         => s_sync_crc_check_err,
            CRC_ERR_VLD     => open,
            CRC_ERR_SRC_RDY => open
        );
    else generate
        s_sync_crc_check_err <= (others => '0');
    end generate;

    -- -------------------------------------------------------------------------
    --  MAC CHECK MODULE
    -- -------------------------------------------------------------------------

    mac_check_en_g : if MAC_CHECK_EN generate
        -- check MAC - latency 5 cycles
        mac_check_i : entity work.RX_MAC_LITE_MAC_CHECK
        generic map (
            REGIONS     => RX_REGIONS,
            REGION_SIZE => RX_REGION_SIZE,
            BLOCK_SIZE  => RX_BLOCK_SIZE,
            ITEM_WIDTH  => RX_ITEM_WIDTH,
            MAC_COUNT   => MAC_COUNT,
            DEVICE      => DEVICE
        )
        port map (
            -- CLOCK AND RESET
            CLK                => RX_CLK,
            RESET              => RX_RESET,
            -- INPUT CONTROL REGISTER INTERFACE
            MAC_CHECK_MODE     => s_ctl_mac_check_mode,
            -- RX MFB INTERFACE
            RX_DATA            => s_cut_data,
            RX_SOF_POS         => s_cut_sof_pos,
            RX_EOF_POS         => s_cut_eof_pos,
            RX_SOF             => s_cut_sof,
            RX_EOF             => s_cut_eof,
            RX_SRC_RDY         => s_cut_src_rdy,
            -- INPUT CAM WRITE INTERFACE
            CAM_WRITE_DATA     => s_cam_write_data,
            CAM_WRITE_ADDR     => s_cam_write_addr,
            CAM_WRITE_EN       => s_cam_write_en,
            CAM_WRITE_RDY      => s_cam_write_rdy,
            -- OUTPUT MVB MAC STATUS INTERFACE
            MAC_STATUS         => s_mac_status,
            MAC_STATUS_VLD     => open,
            MAC_STATUS_SRC_RDY => open
        );

        sh_reg_mac_i : entity work.SH_REG_BASE_STATIC
        generic map (
            NUM_BITS   => 4,
            DATA_WIDTH => RX_REGIONS*MAC_STATUS_WIDTH,
            DEVICE     => DEVICE
        )
        port map (
            CLK        => RX_CLK,
            DIN        => s_mac_status,
            CE         => '1',
            DOUT       => s_sync_mac_status
        );

        sync_mac_g : for r in 0 to RX_REGIONS-1 generate
            s_sync_mac_err(r)      <= s_sync_mac_status(r*MAC_STATUS_WIDTH);
            s_sync_mac_bcast(r)    <= s_sync_mac_status(r*MAC_STATUS_WIDTH+1);
            s_sync_mac_mcast(r)    <= s_sync_mac_status(r*MAC_STATUS_WIDTH+2);
            s_sync_mac_hit_vld(r)  <= s_sync_mac_status(r*MAC_STATUS_WIDTH+3);
            s_sync_mac_hit_addr(r) <= s_sync_mac_status((r+1)*MAC_STATUS_WIDTH-1 downto r*MAC_STATUS_WIDTH+4);
        end generate;
    end generate;

    no_mac_check_en_g : if not MAC_CHECK_EN generate
        s_sync_mac_err      <= (others => '0');
        s_sync_mac_bcast    <= (others => '0');
        s_sync_mac_mcast    <= (others => '0');
        s_sync_mac_hit_vld  <= (others => '0');
        s_sync_mac_hit_addr <= (others => (others => '0'));
        s_cam_write_rdy     <= '1';
    end generate;

    -- -------------------------------------------------------------------------
    --  TIMESTAMP MODULE
    -- -------------------------------------------------------------------------

    timestamp_g : if TIMESTAMP_EN generate
        -- timestamping - latency 1 cycle
        timestamp_i : entity work.RX_MAC_LITE_TIMESTAMP
        generic map (
            REGIONS => RX_REGIONS
        )
        port map (
            -- CLOCK AND RESET
            CLK        => RX_CLK,
            RESET      => RX_RESET,
            -- RX MFB SIGNALS
            RX_EOF     => s_cut_eof,
            RX_SRC_RDY => s_cut_src_rdy,
            -- INPUT TIMESTAMP INTERFACE FROM TSU
            TSU_TS_NS  => TSU_TS_NS,
            TSU_TS_DV  => TSU_TS_DV,
            -- OUTPUT MVB TIMESTAMP INTERFACE ALIGNED ON EOF
            TS_DATA    => s_ts_data,
            TS_VLD     => open,
            TS_SRC_RDY => open
        );

        sh_reg_time_i : entity work.SH_REG_BASE_STATIC
        generic map (
            NUM_BITS   => 8,
            DATA_WIDTH => RX_REGIONS*65,
            DEVICE     => DEVICE
        )
        port map (
            CLK        => RX_CLK,
            DIN        => s_ts_data,
            CE         => '1',
            DOUT       => s_sync_timestamp_ser
        );

        s_sync_timestamp <= slv_array_downto_deser(s_sync_timestamp_ser,RX_REGIONS,65);
    end generate;

    no_timestamp_g : if not TIMESTAMP_EN generate
        s_sync_timestamp <= (others => (others => '0'));
    end generate;

    -- =========================================================================
    --  CREATE METADATA
    -- =========================================================================

    s_sync_error <= s_sync_mii_err or s_sync_crc_err or s_sync_crc_check_err or
                    s_sync_len_min_err or s_sync_len_max_err or s_sync_mac_err;

    sync_metadata_g : for r in 0 to RX_REGIONS-1 generate
        s_sync_metadata(r)(ETH_RX_HDR_LENGTH)         <= std_logic_vector(resize(unsigned(s_sync_frame_len(r)),ETH_RX_HDR_LENGTH_W));
        s_sync_metadata(r)(ETH_RX_HDR_PORT)           <= std_logic_vector(to_unsigned(NETWORK_PORT_ID,ETH_RX_HDR_PORT_W));
        s_sync_metadata(r)(ETH_RX_HDR_ERROR_O)        <= s_sync_error(r);
        s_sync_metadata(r)(ETH_RX_HDR_ERRORFRAME_O)   <= s_sync_mii_err(r);
        s_sync_metadata(r)(ETH_RX_HDR_ERRORMINTU_O)   <= s_sync_len_min_err(r);
        s_sync_metadata(r)(ETH_RX_HDR_ERRORMAXTU_O)   <= s_sync_len_max_err(r);
        s_sync_metadata(r)(ETH_RX_HDR_ERRORCRC_O)     <= s_sync_crc_err(r) or s_sync_crc_check_err(r);
        s_sync_metadata(r)(ETH_RX_HDR_ERRORMAC_O)     <= s_sync_mac_err(r);
        s_sync_metadata(r)(ETH_RX_HDR_BROADCAST_O)    <= s_sync_mac_bcast(r);
        s_sync_metadata(r)(ETH_RX_HDR_MULTICAST_O)    <= s_sync_mac_mcast(r);
        s_sync_metadata(r)(ETH_RX_HDR_HITMACVLD_O)    <= s_sync_mac_hit_vld(r);
        s_sync_metadata(r)(ETH_RX_HDR_HITMAC)         <= std_logic_vector(resize(unsigned(s_sync_mac_hit_addr(r)),ETH_RX_HDR_HITMAC_W));
        s_sync_metadata(r)(ETH_RX_HDR_TIMESTAMPVLD_O) <= s_sync_timestamp(r)(0);
        s_sync_metadata(r)(ETH_RX_HDR_TIMESTAMP)      <= s_sync_timestamp(r)(ETH_RX_HDR_TIMESTAMP_W+1-1 downto 1);
    end generate;

    -- =========================================================================
    --  SPEED METER
    -- =========================================================================

    speed_meter_i : entity work.MFB_SPEED_METER
    generic map (
        REGIONS         => RX_REGIONS,
        REGION_SIZE     => RX_REGION_SIZE,
        BLOCK_SIZE      => RX_BLOCK_SIZE,
        ITEM_WIDTH      => RX_ITEM_WIDTH,
        CNT_TICKS_WIDTH => SM_CNT_TICKS_WIDTH,
        CNT_BYTES_WIDTH => SM_CNT_BYTES_WIDTH,
        CNT_PKTS_WIDTH  => SM_CNT_BYTES_WIDTH,
        DISABLE_ON_CLR  => True,
        COUNT_PACKETS   => True
    )
    port map (
        CLK           => RX_CLK,
        RST           => RX_RESET,

        RX_SOF_POS    => s_sync_sof_pos,
        RX_EOF_POS    => s_sync_eof_pos,
        RX_SOF        => s_sync_sof,
        RX_EOF        => s_sync_eof,
        RX_SRC_RDY    => s_sync_src_rdy,
        RX_DST_RDY    => '1',

        CNT_TICKS     => s_sm_cnt_ticks,
        CNT_TICKS_MAX => s_sm_cnt_ticks_max,
        CNT_BYTES     => s_sm_cnt_bytes,
        CNT_PKT_EOFS  => s_sm_cnt_packets,
        CNT_CLEAR     => s_sm_cnt_clear
    );

    -- =========================================================================
    --  BUFFER
    -- =========================================================================

    mfb_reconf_buf_i : entity work.MFB_RECONFIGURATOR
    generic map (
        RX_REGIONS            => RX_REGIONS,
        RX_REGION_SIZE        => RX_REGION_SIZE,
        RX_BLOCK_SIZE         => RX_BLOCK_SIZE,
        RX_ITEM_WIDTH         => RX_ITEM_WIDTH,
        TX_REGIONS            => BF_REGIONS,
        TX_REGION_SIZE        => BF_REGION_SIZE,
        TX_BLOCK_SIZE         => BF_BLOCK_SIZE,
        TX_ITEM_WIDTH         => BF_ITEM_WIDTH,
        META_WIDTH            => ETH_RX_HDR_WIDTH,
        META_MODE             => 1, -- metadata aligned to EOF
        FIFO_SIZE             => 32,
        FRAMES_OVER_TX_BLOCK  => 1,
        FRAMES_OVER_TX_REGION => 1,
        DEVICE                => DEVICE
    )
    port map (
        CLK        => RX_CLK,
        RESET      => RX_RESET,

        RX_DATA    => s_sync_data,
        RX_META    => slv_array_ser(s_sync_metadata),
        RX_SOF     => s_sync_sof,
        RX_EOF     => s_sync_eof,
        RX_SOF_POS => s_sync_sof_pos,
        RX_EOF_POS => s_sync_eof_pos,
        RX_SRC_RDY => s_sync_src_rdy,
        RX_DST_RDY => s_sync_dst_rdy_dbg, -- debug only

        TX_DATA    => s_bfin_data,
        TX_META    => s_bfin_metadata_ser,
        TX_SOF     => s_bfin_sof,
        TX_EOF     => s_bfin_eof,
        TX_SOF_POS => s_bfin_sof_pos,
        TX_EOF_POS => s_bfin_eof_pos,
        TX_SRC_RDY => s_bfin_src_rdy,
        TX_DST_RDY => '1'
    );

    s_bfin_metadata <= slv_array_deser(s_bfin_metadata_ser,BF_REGIONS);
    s_bfin_err_mask <= s_ctl_error_mask;

    -- ERROR MASKING
    err_mask_g: for rr in 0 to BF_REGIONS-1 generate
        s_bfin_adapter_err_masked(rr) <= s_bfin_metadata(rr)(ETH_RX_HDR_ERRORFRAME_O) and s_bfin_err_mask(0);
        s_bfin_crc_err_masked(rr)     <= s_bfin_metadata(rr)(ETH_RX_HDR_ERRORCRC_O)   and s_bfin_err_mask(1);
        s_bfin_len_min_err_masked(rr) <= s_bfin_metadata(rr)(ETH_RX_HDR_ERRORMINTU_O) and s_bfin_err_mask(2);
        s_bfin_len_max_err_masked(rr) <= s_bfin_metadata(rr)(ETH_RX_HDR_ERRORMAXTU_O) and s_bfin_err_mask(3);
        s_bfin_mac_err_masked(rr)     <= s_bfin_metadata(rr)(ETH_RX_HDR_ERRORMAC_O)   and s_bfin_err_mask(4);
    end generate;

    s_bfin_error <= (s_bfin_adapter_err_masked or s_bfin_crc_err_masked or
                    s_bfin_len_min_err_masked or s_bfin_len_max_err_masked or
                    s_bfin_mac_err_masked) or (not s_ctl_enable);

    s_bfin_metactrl <= s_ctl_error_mask & s_ctl_enable;

    buffer_i : entity work.RX_MAC_LITE_BUFFER
    generic map (
        REGIONS        => BF_REGIONS,
        REGION_SIZE    => BF_REGION_SIZE,
        BLOCK_SIZE     => BF_BLOCK_SIZE,
        ITEM_WIDTH     => BF_ITEM_WIDTH,
        META_WIDTH     => ETH_RX_HDR_WIDTH,
        METACTRL_WIDTH => 6,     -- error_mask + enable
        META_ALIGN2SOF => false, -- (BF_REGIONS>1),
        DFIFO_ITEMS    => DFIFO_ITEMS,
        MFIFO_ITEMS    => MFIFO_ITEMS,
        MFIFO_RAM_TYPE => "BRAM",
        DEVICE         => DEVICE
    )
    port map (
        RX_CLK          => RX_CLK,
        RX_RESET        => RX_RESET,

        RX_DATA         => s_bfin_data,
        RX_SOF_POS      => s_bfin_sof_pos,
        RX_EOF_POS      => s_bfin_eof_pos,
        RX_SOF          => s_bfin_sof,
        RX_EOF          => s_bfin_eof,
        RX_ERROR        => s_bfin_error,
        RX_METADATA     => s_bfin_metadata,
        RX_METACTRL     => s_bfin_metactrl,
        RX_SRC_RDY      => s_bfin_src_rdy,

        BUFFER_STATUS   => s_buffer_status,
        STAT_BUFFER_OVF => s_stin_buffer_ovf,
        STAT_DISCARD    => s_stin_discarded,
        STAT_METADATA   => s_stin_metadata,
        STAT_METACTRL   => s_stin_metactrl,
        STAT_VALID      => s_stin_valid,

        TX_CLK          => TX_CLK,
        TX_RESET        => TX_RESET,

        TX_MFB_DATA     => s_buf_mfb_data,
        TX_MFB_SOF_POS  => s_buf_mfb_sof_pos,
        TX_MFB_EOF_POS  => s_buf_mfb_eof_pos,
        TX_MFB_SOF      => s_buf_mfb_sof,
        TX_MFB_EOF      => s_buf_mfb_eof,
        TX_MFB_SRC_RDY  => s_buf_mfb_src_rdy,
        TX_MFB_DST_RDY  => s_buf_mfb_dst_rdy,

        TX_MVB_DATA     => s_buf_mvb_data,
        TX_MVB_VLD      => s_buf_mvb_vld,
        TX_MVB_SRC_RDY  => s_buf_mvb_src_rdy,
        TX_MVB_DST_RDY  => s_buf_mvb_dst_rdy
    );

    s_stin_err_mask <= s_stin_metactrl(6-1 downto 1);
    s_stin_enable   <= s_stin_metactrl(0);

    -- =========================================================================
    --  MFB RECONFIGURATOR + MVB RECONFIGURATOR
    -- =========================================================================

    mfb_reconf_i : entity work.MFB_RECONFIGURATOR
    generic map (
        RX_REGIONS            => BF_REGIONS,
        RX_REGION_SIZE        => BF_REGION_SIZE,
        RX_BLOCK_SIZE         => BF_BLOCK_SIZE,
        RX_ITEM_WIDTH         => BF_ITEM_WIDTH,
        TX_REGIONS            => TX_REGIONS,
        TX_REGION_SIZE        => TX_REGION_SIZE,
        TX_BLOCK_SIZE         => TX_BLOCK_SIZE,
        TX_ITEM_WIDTH         => TX_ITEM_WIDTH,
        FIFO_SIZE             => 32,
        FRAMES_OVER_TX_BLOCK  => 1,
        FRAMES_OVER_TX_REGION => 1,
        DEVICE                => DEVICE
    )
    port map (
        CLK        => TX_CLK,
        RESET      => TX_RESET,

        RX_DATA    => s_buf_mfb_data,
        RX_SOF     => s_buf_mfb_sof,
        RX_EOF     => s_buf_mfb_eof,
        RX_SOF_POS => s_buf_mfb_sof_pos,
        RX_EOF_POS => s_buf_mfb_eof_pos,
        RX_SRC_RDY => s_buf_mfb_src_rdy,
        RX_DST_RDY => s_buf_mfb_dst_rdy,

        TX_DATA    => TX_MFB_DATA,
        TX_SOF     => TX_MFB_SOF,
        TX_EOF     => TX_MFB_EOF,
        TX_SOF_POS => TX_MFB_SOF_POS,
        TX_EOF_POS => TX_MFB_EOF_POS,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

    mvb_wire_g : if (BF_REGIONS = TX_REGIONS) generate
        TX_MVB_DATA       <= s_buf_mvb_data;
        TX_MVB_VLD        <= s_buf_mvb_vld;
        TX_MVB_SRC_RDY    <= s_buf_mvb_src_rdy;
        s_buf_mvb_dst_rdy <= TX_MVB_DST_RDY;
    end generate;

    mvb_shake_g : if (BF_REGIONS > TX_REGIONS) generate
        mvb_shake_i : entity work.MVB_SHAKEDOWN
        generic map (
            RX_ITEMS    => BF_REGIONS,
            TX_ITEMS    => TX_REGIONS,
            ITEM_WIDTH  => ETH_RX_HDR_WIDTH,
            SHAKE_PORTS => 1
        )
        port map (
            CLK        => TX_CLK,
            RESET      => TX_RESET,

            RX_DATA    => s_buf_mvb_data,
            RX_VLD     => s_buf_mvb_vld,
            RX_SRC_RDY => s_buf_mvb_src_rdy,
            RX_DST_RDY => s_buf_mvb_dst_rdy,

            TX_DATA    => TX_MVB_DATA,
            TX_VLD     => TX_MVB_VLD,
            TX_NEXT    => (others => TX_MVB_DST_RDY)
        );
        TX_MVB_SRC_RDY <= or TX_MVB_VLD;
    end generate;

    mvb_resize_g : if (BF_REGIONS < TX_REGIONS) generate
        TX_MVB_DATA       <= std_logic_vector(resize(unsigned(s_buf_mvb_data),TX_MVB_DATA'length));
        TX_MVB_VLD        <= std_logic_vector(resize(unsigned(s_buf_mvb_vld),TX_MVB_VLD'length));
        TX_MVB_SRC_RDY    <= s_buf_mvb_src_rdy;
        s_buf_mvb_dst_rdy <= TX_MVB_DST_RDY;
    end generate;

    -- =========================================================================
    --  STATISTICS UNIT
    -- =========================================================================

    stin_metadata_unpack_g : for i in 0 to BF_REGIONS-1 generate
        s_stin_mii_err_masked(i) <= s_stin_metadata(i)(ETH_RX_HDR_ERRORFRAME_O) and s_stin_err_mask(0);
        s_stin_crc_err(i)        <= s_stin_metadata(i)(ETH_RX_HDR_ERRORCRC_O);
        s_stin_crc_err_masked(i) <= s_stin_metadata(i)(ETH_RX_HDR_ERRORCRC_O) and s_stin_err_mask(1);
        s_stin_mac_err(i)        <= s_stin_metadata(i)(ETH_RX_HDR_ERRORMAC_O);
        s_stin_mac_err_masked(i) <= s_stin_metadata(i)(ETH_RX_HDR_ERRORMAC_O) and s_stin_err_mask(4);
        s_stin_len_err_masked(i) <= (s_stin_metadata(i)(ETH_RX_HDR_ERRORMINTU_O) and s_stin_err_mask(2)) or
                                    (s_stin_metadata(i)(ETH_RX_HDR_ERRORMAXTU_O) and s_stin_err_mask(3));
        s_stin_mac_bcast(i)      <= s_stin_metadata(i)(ETH_RX_HDR_BROADCAST_O);
        s_stin_mac_mcast(i)      <= s_stin_metadata(i)(ETH_RX_HDR_MULTICAST_O);
        s_stin_frame_len(i)      <= std_logic_vector(resize(unsigned(s_stin_metadata(i)(ETH_RX_HDR_LENGTH)),LEN_WIDTH));
        s_stin_len_min_err(i)    <= s_stin_metadata(i)(ETH_RX_HDR_ERRORMINTU_O);
        s_stin_len_max_err(i)    <= s_stin_metadata(i)(ETH_RX_HDR_ERRORMAXTU_O);
        s_stin_drop_off(i)       <= s_stin_valid(i) and not s_stin_enable;
    end generate;

    stat_unit_i : entity work.RX_MAC_LITE_STAT_UNIT
    generic map (
        REGIONS            => BF_REGIONS,
        REGION_SIZE        => BF_REGION_SIZE,
        BLOCK_SIZE         => BF_BLOCK_SIZE,
        ITEM_WIDTH         => BF_ITEM_WIDTH,

        INBANDFCS          => INBANDCRC,
        LEN_WIDTH          => LEN_WIDTH,
        CNT_IN_DSP         => True,
        DEVICE             => DEVICE,
        -- Counters setup
        SIZE_EN            => true,
        LEN_HISTOGRAM_EN   => true
    )
    port map (
        CLK                    => RX_CLK,
        RESET                  => RX_RESET,
        -- CONTROL INTERFACE
        CTRL_STAT_EN           => '1',
        CTRL_SW_RESET          => s_ctl_stat_sw_reset,
        CTRL_TAKE_SNAPSHOT     => s_ctl_stat_take_snapshot,
        CTRL_READ_SNAPSHOT     => s_ctl_stat_read_snapshot,
        -- INPUT STATISTICS FLAGS
        IN_FRAME_RECEIVED      => s_stin_valid,
        IN_FRAME_DISCARDED     => s_stin_discarded,
        IN_BUFFER_OVF          => s_stin_buffer_ovf,
        IN_FRAME_DROP_OFF      => s_stin_drop_off,
        IN_FRAME_ERROR_MASKED  => s_stin_mii_err_masked,
        IN_CRC_ERROR           => s_stin_crc_err,
        IN_CRC_ERROR_MASKED    => s_stin_crc_err_masked,
        IN_MAC_ERROR           => s_stin_mac_err,
        IN_MAC_ERROR_MASKED    => s_stin_mac_err_masked,
        IN_LEN_ERROR_MASKED    => s_stin_len_err_masked,
        IN_MAC_BCAST           => s_stin_mac_bcast,
        IN_MAC_MCAST           => s_stin_mac_mcast,
        IN_FRAME_LEN           => s_stin_frame_len,
        IN_LEN_BELOW_MIN       => s_stin_len_min_err,
        IN_LEN_OVER_MTU        => s_stin_len_max_err,
        IN_STAT_FLAGS_VLD      => s_stin_valid,
        -- OUTPUT OF STATISTICS COUNTERS
        OUT_STAT_VLD           => open,
        OUT_BASE_TOTAL         => s_stat_out_base_total,
        OUT_BASE_PASSED        => s_stat_out_base_passed,
        OUT_BASE_DROPPED       => s_stat_out_base_dropped,
        OUT_BASE_DROP_OFF      => s_stat_out_base_drop_off,
        OUT_BASE_DROP_OVF      => s_stat_out_base_drop_ovf,
        OUT_BASE_DROP_FLT      => s_stat_out_base_drop_flt,
        OUT_BASE_DROP_ERR      => s_stat_out_base_drop_err,
        OUT_BASE_ERR_LEN       => s_stat_out_base_err_len,
        OUT_BASE_ERR_MII       => s_stat_out_base_err_mii,
        OUT_BASE_ERR_CRC       => s_stat_out_base_err_crc,
        OUT_RX_BYTES           => s_stat_out_rx_bytes,
        OUT_TX_BYTES           => s_stat_out_tx_bytes,
        OUT_RFC_CRC_ERR        => s_stat_out_rfc_crc_err,
        OUT_RFC_MAC_ERR        => s_stat_out_rfc_mac_err,
        OUT_RFC_OVER_MTU       => s_stat_out_rfc_over_mtu,
        OUT_RFC_BELOW_MIN      => s_stat_out_rfc_below_min,
        OUT_RFC_MAC_BCAST      => s_stat_out_rfc_mac_bcast,
        OUT_RFC_MAC_MCAST      => s_stat_out_rfc_mac_mcast,
        OUT_RFC_FRAGMENT       => s_stat_out_rfc_fragment,
        OUT_RFC_JABBER         => s_stat_out_rfc_jabber,
        OUT_HIST_UNDERSIZE     => s_stat_out_hist_undersize,
        OUT_HIST_64            => s_stat_out_hist_64,
        OUT_HIST_65_127        => s_stat_out_hist_65_127,
        OUT_HIST_128_255       => s_stat_out_hist_128_255,
        OUT_HIST_256_511       => s_stat_out_hist_256_511,
        OUT_HIST_512_1023      => s_stat_out_hist_512_1023,
        OUT_HIST_1024_1518     => s_stat_out_hist_1024_1518,
        OUT_HIST_OVER_1518     => s_stat_out_hist_over_1518,
        OUT_HIST_1519_2047     => s_stat_out_hist_1519_2047,
        OUT_HIST_2048_4095     => s_stat_out_hist_2048_4095,
        OUT_HIST_4096_8191     => s_stat_out_hist_4096_8191,
        OUT_HIST_OVER_8191     => s_stat_out_hist_over_8191
    );

    -- =========================================================================
    --  CONTROL UNIT
    -- =========================================================================

    ctrl_unit_i : entity work.RX_MAC_LITE_CTRL_UNIT
    generic map (
        LEN_WIDTH          => LEN_WIDTH,
        INBANDFCS          => INBANDCRC,
        MAC_COUNT          => MAC_COUNT,
        SM_CNT_TICKS_WIDTH => SM_CNT_TICKS_WIDTH,
        SM_CNT_BYTES_WIDTH => SM_CNT_BYTES_WIDTH,
        DEVICE             => DEVICE
    )
    port map (
        CLK                     => RX_CLK,
        RESET                   => RX_RESET,
        -- MI32 INTERFACE
        MI_CLK                  => MI_CLK,
        MI_RESET                => MI_RESET,
        MI_DWR                  => MI_DWR,
        MI_ADDR                 => MI_ADDR,
        MI_RD                   => MI_RD,
        MI_WR                   => MI_WR,
        MI_BE                   => MI_BE,
        MI_DRD                  => MI_DRD,
        MI_ARDY                 => MI_ARDY,
        MI_DRDY                 => MI_DRDY,
        -- OTHERS CONTROL INPUT INTERFACE
        LINK_STATUS             => ADAPTER_LINK_UP,
        BUFFER_STATUS           => s_buffer_status,
        -- SPEED METER INTERFACE
        SM_CNT_TICKS            => s_sm_cnt_ticks,
        SM_CNT_TICKS_MAX        => s_sm_cnt_ticks_max,
        SM_CNT_BYTES            => s_sm_cnt_bytes,
        SM_CNT_PACKETS          => s_sm_cnt_packets,
        SM_CNT_CLEAR            => s_sm_cnt_clear,
        -- CAM WRITE INTERFACE
        CAM_WRITE_DATA          => s_cam_write_data,
        CAM_WRITE_ADDR          => s_cam_write_addr,
        CAM_WRITE_EN            => s_cam_write_en,
        CAM_WRITE_RDY           => s_cam_write_rdy,
        -- CONTROL INTERFACE
        CTL_SW_RESET            => s_ctl_stat_sw_reset,
        CTL_TAKE_SNAPSHOT       => s_ctl_stat_take_snapshot,
        CTL_READ_SNAPSHOT       => s_ctl_stat_read_snapshot,
        CTL_ENABLE              => s_ctl_enable,
        CTL_ERROR_MASK          => s_ctl_error_mask,
        CTL_FRAME_LEN_MAX       => s_ctl_frame_len_max,
        CTL_FRAME_LEN_MIN       => s_ctl_frame_len_min,
        CTL_MAC_CHECK_MODE      => s_ctl_mac_check_mode,
        -- INPUT OF STATISTICS
        STAT_BASE_TOTAL         => s_stat_out_base_total,
        STAT_BASE_PASSED        => s_stat_out_base_passed,
        STAT_BASE_DROPPED       => s_stat_out_base_dropped,
        STAT_BASE_DROP_OFF      => s_stat_out_base_drop_off,
        STAT_BASE_DROP_OVF      => s_stat_out_base_drop_ovf,
        STAT_BASE_DROP_FLT      => s_stat_out_base_drop_flt,
        STAT_BASE_DROP_ERR      => s_stat_out_base_drop_err,
        STAT_BASE_ERR_LEN       => s_stat_out_base_err_len,
        STAT_BASE_ERR_MII       => s_stat_out_base_err_mii,
        STAT_BASE_ERR_CRC       => s_stat_out_base_err_crc,
        STAT_RX_BYTES           => s_stat_out_rx_bytes,
        STAT_TX_BYTES           => s_stat_out_tx_bytes,
        STAT_RFC_CRC_ERR        => s_stat_out_rfc_crc_err,
        STAT_RFC_MAC_ERR        => s_stat_out_rfc_mac_err,
        STAT_RFC_OVER_MTU       => s_stat_out_rfc_over_mtu,
        STAT_RFC_BELOW_MIN      => s_stat_out_rfc_below_min,
        STAT_RFC_MAC_BCAST      => s_stat_out_rfc_mac_bcast,
        STAT_RFC_MAC_MCAST      => s_stat_out_rfc_mac_mcast,
        STAT_RFC_FRAGMENT       => s_stat_out_rfc_fragment,
        STAT_RFC_JABBER         => s_stat_out_rfc_jabber,
        STAT_HIST_UNDERSIZE     => s_stat_out_hist_undersize,
        STAT_HIST_64            => s_stat_out_hist_64,
        STAT_HIST_65_127        => s_stat_out_hist_65_127,
        STAT_HIST_128_255       => s_stat_out_hist_128_255,
        STAT_HIST_256_511       => s_stat_out_hist_256_511,
        STAT_HIST_512_1023      => s_stat_out_hist_512_1023,
        STAT_HIST_1024_1518     => s_stat_out_hist_1024_1518,
        STAT_HIST_OVER_1518     => s_stat_out_hist_over_1518,
        STAT_HIST_1519_2047     => s_stat_out_hist_1519_2047,
        STAT_HIST_2048_4095     => s_stat_out_hist_2048_4095,
        STAT_HIST_4096_8191     => s_stat_out_hist_4096_8191,
        STAT_HIST_OVER_8191     => s_stat_out_hist_over_8191
    );

end architecture;
