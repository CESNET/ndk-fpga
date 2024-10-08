-- rx_dma_calypte.vhd:  top-level of the RX DMA module
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity RX_DMA_CALYPTE is

    generic (
        DEVICE : string := "ULTRASCALE";

        -- Width of MI bus
        MI_WIDTH : natural := 32;

        -- User Logic MFB configuration
        USER_RX_MFB_REGIONS     : natural := 1;
        USER_RX_MFB_REGION_SIZE : natural := 8;
        USER_RX_MFB_BLOCK_SIZE  : natural := 8;
        USER_RX_MFB_ITEM_WIDTH  : natural := 8;

        -- PCIe MFB configuration
        PCIE_UP_MFB_REGIONS     : natural := 2;
        PCIE_UP_MFB_REGION_SIZE : natural := 1;
        PCIE_UP_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_UP_MFB_ITEM_WIDTH  : natural := 32;

        -- Total number of DMA Channels within this DMA Endpoint
        CHANNELS : natural := 8;

        -- * Width of Software and Hardware Descriptor/Header Pointer
        -- * Defines width of signals used for these values in DMA Module
        -- * Affects logic complexity
        -- * Maximum value: 32 (restricted by size of pointer MI registers)
        POINTER_WIDTH  : natural := 16;

        -- Width of RAM address
        SW_ADDR_WIDTH  : natural := 64;

        -- Actual width of packet and byte counters
        CNTRS_WIDTH    : natural := 64;

        HDR_META_WIDTH : natural := 24;

        -- * Maximum size of a packet (in bytes).
        -- * Defines width of Packet length signals.
        -- * Maximum allowed value is 2**16 - 1
        PKT_SIZE_MAX : natural := 2**16 - 1;

        TRBUF_FIFO_EN           : boolean := FALSE;
        TRBUF_REG_EN            : boolean := FALSE
        );

    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =====================================================================
        -- MI interface for SW access
        -- =====================================================================
        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic;

        -- =========================================================================================================
        -- MFB input interface
        -- =========================================================================================================
        USER_RX_MFB_META_HDR_META : in  std_logic_vector(HDR_META_WIDTH-1 downto 0)       := (others => '0');
        USER_RX_MFB_META_CHAN     : in  std_logic_vector(log2(CHANNELS)-1 downto 0)       := (others => '0');

        USER_RX_MFB_DATA     : in  std_logic_vector(USER_RX_MFB_REGIONS*USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE*USER_RX_MFB_ITEM_WIDTH-1 downto 0);
        USER_RX_MFB_SOF      : in  std_logic_vector(USER_RX_MFB_REGIONS - 1 downto 0);
        USER_RX_MFB_EOF      : in  std_logic_vector(USER_RX_MFB_REGIONS - 1 downto 0);
        USER_RX_MFB_SOF_POS  : in  std_logic_vector(USER_RX_MFB_REGIONS*max(1, log2(USER_RX_MFB_REGION_SIZE))-1 downto 0);
        USER_RX_MFB_EOF_POS  : in  std_logic_vector(USER_RX_MFB_REGIONS*max(1, log2(USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE))-1 downto 0);
        USER_RX_MFB_SRC_RDY  : in  std_logic;
        USER_RX_MFB_DST_RDY  : out std_logic;


        -- =========================================================================================================
        -- MFB output interface
        -- =========================================================================================================
        PCIE_UP_MFB_DATA    : out std_logic_vector(PCIE_UP_MFB_REGIONS*PCIE_UP_MFB_REGION_SIZE*PCIE_UP_MFB_BLOCK_SIZE*PCIE_UP_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_UP_MFB_META    : out std_logic_vector(PCIE_UP_MFB_REGIONS*PCIE_RQ_META_WIDTH - 1 downto 0);
        PCIE_UP_MFB_SOF     : out std_logic_vector(PCIE_UP_MFB_REGIONS - 1 downto 0);
        PCIE_UP_MFB_EOF     : out std_logic_vector(PCIE_UP_MFB_REGIONS - 1 downto 0);
        PCIE_UP_MFB_SOF_POS : out std_logic_vector(PCIE_UP_MFB_REGIONS*max(1, log2(PCIE_UP_MFB_REGION_SIZE))-1 downto 0);
        PCIE_UP_MFB_EOF_POS : out std_logic_vector(PCIE_UP_MFB_REGIONS*max(1, log2(PCIE_UP_MFB_REGION_SIZE*PCIE_UP_MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_UP_MFB_SRC_RDY : out std_logic;
        PCIE_UP_MFB_DST_RDY : in  std_logic
        );

end entity;

architecture FULL of RX_DMA_CALYPTE is

    --=============================================================================================================
    -- Internal MFB configuration
    --=============================================================================================================
    constant MFB_REGION_SIZE_TRBUF2INS : natural := 1;
    -- the BLOCK_SIZE is set in this way hecause the transition buffer takes 4 MFB words and puts them all on the
    -- output
    constant MFB_BLOCK_SIZE_TRBUF2INS  : natural := (1024 / PCIE_UP_MFB_DATA'length)*USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE;
    constant MFB_ITEM_WIDTH_TRBUF2INS  : natural := USER_RX_MFB_ITEM_WIDTH;

    constant MFB_REGION_SIZE_INBUF2TRBUF : natural := 1;
    -- the BLOCK_SIZE is adjusted according to the parameters of the bus, there is always one packet in a single
    -- word and it also begins on the LSB of the word
    constant MFB_BLOCK_SIZE_INBUF2TRBUF  : natural := USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE;
    constant MFB_ITEM_WIDTH_INBUF2TRBUF  : natural := USER_RX_MFB_ITEM_WIDTH;

    -- the lengh of the PCIe transaction
    constant BUFFERED_DATA_SIZE : natural := 128;
    --=============================================================================================================

    signal start_req_chan : std_logic_vector((log2(CHANNELS)-1) downto 0);
    signal start_req_vld  : std_logic;
    signal start_req_done : std_logic;

    signal stop_req_chan : std_logic_vector((log2(CHANNELS)-1) downto 0);
    signal stop_req_vld  : std_logic;
    signal stop_req_done : std_logic;

    signal hdrm_data_rd_chan : std_logic_vector((log2(CHANNELS)-1) downto 0);
    signal hdrm_hdr_rd_chan  : std_logic_vector((log2(CHANNELS)-1) downto 0);
    signal hdrm_dba_rd_data  : std_logic_vector(SW_ADDR_WIDTH-1 downto 0);
    signal hdrm_hba_rd_data  : std_logic_vector(SW_ADDR_WIDTH-1 downto 0);
    signal hdrm_dpm_rd_data  : std_logic_vector(POINTER_WIDTH-1 downto 0);
    signal hdrm_hpm_rd_data  : std_logic_vector(POINTER_WIDTH-1 downto 0);
    signal hdrm_sdp_rd_data  : std_logic_vector(POINTER_WIDTH-1 downto 0);
    signal hdrm_shp_rd_data  : std_logic_vector(POINTER_WIDTH-1 downto 0);

    signal hdrm_hdp_update_chan : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal hdrm_hdp_update_data : std_logic_vector(POINTER_WIDTH-1 downto 0);
    signal hdrm_hdp_update_en   : std_logic;
    signal hdrm_hhp_update_chan : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal hdrm_hhp_update_data : std_logic_vector(POINTER_WIDTH-1 downto 0);
    signal hdrm_hhp_update_en   : std_logic;

    signal hdrm_dma_pcie_hdr_size    : std_logic;
    signal hdrm_dma_pcie_hdr         : std_logic_vector (127 downto 0);
    signal hdrm_dma_pcie_hdr_src_rdy : std_logic;
    signal hdrm_dma_pcie_hdr_dst_rdy : std_logic;

    signal hdrm_data_pcie_hdr_size    : std_logic;
    signal hdrm_data_pcie_hdr         : std_logic_vector (127 downto 0);
    signal hdrm_data_pcie_hdr_src_rdy : std_logic;
    signal hdrm_data_pcie_hdr_dst_rdy : std_logic;

    signal hdrm_pkt_drop         : std_logic;
    signal hdrm_dma_hdr_data     : std_logic_vector (63 downto 0);
    signal hdrm_dma_hdr_src_rdy  : std_logic;
    signal hdrm_dma_hdr_dst_rdy  : std_logic;

    signal hdrm_pkt_sent_chan  : std_logic_vector((log2(CHANNELS)-1) downto 0);
    signal hdrm_pkt_sent_inc   : std_logic;
    signal hdrm_pkt_disc_inc   : std_logic;
    signal hdrm_pkt_sent_bytes : std_logic_vector((log2(PKT_SIZE_MAX+1)-1) downto 0);

    signal trbuf_fifo_tx_data    : std_logic_vector(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS*MFB_ITEM_WIDTH_TRBUF2INS-1 downto 0);
    signal trbuf_fifo_tx_sof_pos : std_logic_vector (max(1, log2(MFB_REGION_SIZE_TRBUF2INS))-1 downto 0);
    signal trbuf_fifo_tx_eof_pos : std_logic_vector (max(1, log2(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS))-1 downto 0);
    signal trbuf_fifo_tx_sof     : std_logic;
    signal trbuf_fifo_tx_eof     : std_logic;
    signal trbuf_fifo_tx_src_rdy : std_logic;
    signal trbuf_fifo_tx_dst_rdy : std_logic;

    signal trbuf_fifo_rx_data    : std_logic_vector(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS*MFB_ITEM_WIDTH_TRBUF2INS-1 downto 0);
    signal trbuf_fifo_rx_sof_pos : std_logic_vector (max(1, log2(MFB_REGION_SIZE_TRBUF2INS))-1 downto 0);
    signal trbuf_fifo_rx_eof_pos : std_logic_vector (max(1, log2(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS))-1 downto 0);
    signal trbuf_fifo_rx_sof     : std_logic;
    signal trbuf_fifo_rx_eof     : std_logic;
    signal trbuf_fifo_rx_src_rdy : std_logic;
    signal trbuf_fifo_rx_dst_rdy : std_logic;

    -- =============================================================================================
    -- Frame length checker ---> Transaction buffer
    -- =============================================================================================
    signal mfb_data_lng_check    : std_logic_vector(MFB_REGION_SIZE_INBUF2TRBUF*MFB_BLOCK_SIZE_INBUF2TRBUF*MFB_ITEM_WIDTH_INBUF2TRBUF-1 downto 0);
    signal mfb_sof_lng_check     : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal mfb_eof_lng_check     : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal mfb_eof_pos_lng_check : std_logic_vector(max(1, log2(MFB_REGION_SIZE_INBUF2TRBUF*MFB_BLOCK_SIZE_INBUF2TRBUF))-1 downto 0);
    signal mfb_src_rdy_lng_check : std_logic;
    signal mfb_dst_rdy_lng_check : std_logic;

    signal stat_frame_lng : std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal stat_frame_lng_max_err : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal stat_frame_lng_min_err : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal stat_frame_lng_ovf_err : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);

    -- =============================================================================================
    -- Input buffer ---> Frame length checker
    -- =============================================================================================
    signal mfb_data_inbuf    : std_logic_vector(USER_RX_MFB_REGIONS*USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE*USER_RX_MFB_ITEM_WIDTH-1 downto 0);
    signal mfb_sof_inbuf     : std_logic;
    signal mfb_eof_inbuf     : std_logic;
    signal mfb_sof_pos_inbuf : std_logic_vector(max(1, USER_RX_MFB_REGIONS*log2(USER_RX_MFB_REGION_SIZE))-1 downto 0);
    signal mfb_eof_pos_inbuf : std_logic_vector(max(1, USER_RX_MFB_REGIONS*log2(USER_RX_MFB_REGION_SIZE*USER_RX_MFB_BLOCK_SIZE))-1 downto 0);
    signal mfb_src_rdy_inbuf : std_logic;
    signal mfb_dst_rdy_inbuf : std_logic;


    -- additional DST rdy signals which control the transfers of data between the Header management logic and Data
    -- path logic
    signal data_path_dst_rdy : std_logic;
    signal hdr_log_dst_rdy   : std_logic;

    --==============================================================================================
    -- Debug signals for the RX DMA
    --==============================================================================================
    -- attribute mark_debug : string;
    -- attribute mark_debug of USER_RX_MFB_META_HDR_META : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_META_CHAN     : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_META_PKT_SIZE : signal is "true";

    -- attribute mark_debug of USER_RX_MFB_DATA    : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_SOF     : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_EOF     : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_SOF_POS : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_EOF_POS : signal is "true";
    -- attribute mark_debug of USER_RX_MFB_SRC_RDY : signal is "true";
    -- attribute mark_debug of hdr_log_dst_rdy     : signal is "true";
    -- attribute mark_debug of data_path_dst_rdy   : signal is "true";

    -- attribute mark_debug of PCIE_UP_MFB_DATA    : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_SOF     : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_EOF     : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_SOF_POS : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_EOF_POS : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_SRC_RDY : signal is "true";
    -- attribute mark_debug of PCIE_UP_MFB_DST_RDY : signal is "true";

    -- attribute mark_debug of hdrm_pkt_sent_chan  : signal is "true";
    -- attribute mark_debug of hdrm_pkt_sent_inc   : signal is "true";
    -- attribute mark_debug of hdrm_pkt_disc_inc   : signal is "true";
    -- attribute mark_debug of hdrm_pkt_sent_bytes : signal is "true";

    -- attribute mark_debug of hdrm_pcie_hdr_type    : signal is "true";
    -- attribute mark_debug of hdrm_pcie_hdr_data    : signal is "true";
    -- attribute mark_debug of hdrm_pcie_hdr_src_rdy_dma_hdr : signal is "true";
    -- attribute mark_debug of hdrm_pcie_hdr_src_rdy_data_tran : signal is "true";
    -- attribute mark_debug of hdrm_pcie_hdr_dst_rdy : signal is "true";

    -- attribute mark_debug of hdrm_pkt_drop        : signal is "true";
    -- attribute mark_debug of hdrm_dma_hdr_data    : signal is "true";
    -- attribute mark_debug of hdrm_dma_hdr_src_rdy : signal is "true";
    -- attribute mark_debug of hdrm_dma_hdr_dst_rdy : signal is "true";

    -- attribute mark_debug of trbuf_fifo_tx_data    : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_sof     : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_eof     : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_sof_pos : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_eof_pos : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_src_rdy : signal is "true";
    -- attribute mark_debug of trbuf_fifo_tx_dst_rdy : signal is "true";

    -- attribute mark_debug of mfb_src_rdy_inbuf : signal is "true";
    -- attribute mark_debug of mfb_dst_rdy_inbuf : signal is "true";
    -- attribute mark_debug of stop_req_chan  : signal is "true";
    -- attribute mark_debug of stop_req_vld   : signal is "true";
    -- attribute mark_debug of stop_req_done  : signal is "true";
    -- attribute mark_debug of start_req_chan : signal is "true";
    -- attribute mark_debug of start_req_vld  : signal is "true";
    -- attribute mark_debug of start_req_done : signal is "true";
begin

    assert (PKT_SIZE_MAX < 2**16)
        report "RX_LL_DMA: the packet size must be set to the number less than 2^16"
        severity FAILURE;

    assert (USER_RX_MFB_REGIONS = 1 and (USER_RX_MFB_REGION_SIZE = 4 or USER_RX_MFB_REGION_SIZE = 8) and USER_RX_MFB_BLOCK_SIZE = 8 and USER_RX_MFB_ITEM_WIDTH = 8)
        report "RX_LL_DMA: The design is not set for such User Logic MFB configuration, the valid are: MFB#(1,4,8,8), MFB#(1,8,8,8)."
        severity FAILURE;

    assert ((PCIE_UP_MFB_REGIONS = 1 or PCIE_UP_MFB_REGIONS = 2) and PCIE_UP_MFB_REGION_SIZE = 1 and PCIE_UP_MFB_BLOCK_SIZE = 8 and PCIE_UP_MFB_ITEM_WIDTH = 32)
        report "RX_LL_DMA: The design is not set for such PCIe MFB configuration, the valid are: MFB#(1,1,8,32), MFB#(2,1,8,32)."
        severity FAILURE;

    rx_dma_sw_manager_i : entity work.RX_DMA_CALYPTE_SW_MANAGER
        generic map (
            DEVICE             => DEVICE,
            CHANNELS           => CHANNELS,
            POINTER_WIDTH      => POINTER_WIDTH,
            SW_ADDR_WIDTH      => SW_ADDR_WIDTH,
            RECV_PKT_CNT_WIDTH => CNTRS_WIDTH,
            RECV_BTS_CNT_WIDTH => CNTRS_WIDTH,
            DISC_PKT_CNT_WIDTH => CNTRS_WIDTH,
            DISC_BTS_CNT_WIDTH => CNTRS_WIDTH,
            PKT_SIZE_MAX       => PKT_SIZE_MAX,
            MI_WIDTH           => MI_WIDTH)
        port map (
            CLK   => CLK,
            RESET => RESET,

            MI_ADDR => MI_ADDR,
            MI_DWR  => MI_DWR,
            MI_BE   => MI_BE,
            MI_RD   => MI_RD,
            MI_WR   => MI_WR,
            MI_DRD  => MI_DRD,
            MI_ARDY => MI_ARDY,
            MI_DRDY => MI_DRDY,

            PKT_SENT_CHAN     => hdrm_pkt_sent_chan,
            PKT_SENT_INC      => hdrm_pkt_sent_inc,
            PKT_SENT_BYTES    => hdrm_pkt_sent_bytes,
            PKT_DISCARD_CHAN  => hdrm_pkt_sent_chan,
            PKT_DISCARD_INC   => hdrm_pkt_disc_inc,
            PKT_DISCARD_BYTES => hdrm_pkt_sent_bytes,

            START_REQ_CHAN => start_req_chan,
            START_REQ_VLD  => start_req_vld,
            START_REQ_ACK  => start_req_done,

            STOP_FORCE_CHAN => open,
            STOP_FORCE      => open,

            STOP_REQ_CHAN => stop_req_chan,
            STOP_REQ_VLD  => stop_req_vld,
            STOP_REQ_ACK  => stop_req_done,

            ENABLED_CHAN => open,

            SDP_RD_CHAN => hdrm_data_rd_chan,
            SDP_RD_DATA => hdrm_sdp_rd_data,
            SHP_RD_CHAN => hdrm_hdr_rd_chan,
            SHP_RD_DATA => hdrm_shp_rd_data,

            HDP_WR_CHAN => hdrm_hdp_update_chan,
            HDP_WR_DATA => hdrm_hdp_update_data,
            HDP_WR_EN   => hdrm_hdp_update_en,
            HHP_WR_CHAN => hdrm_hhp_update_chan,
            HHP_WR_DATA => hdrm_hhp_update_data,
            HHP_WR_EN   => hdrm_hhp_update_en,

            DBA_RD_CHAN => hdrm_data_rd_chan,
            DBA_RD_DATA => hdrm_dba_rd_data,
            HBA_RD_CHAN => hdrm_hdr_rd_chan,
            HBA_RD_DATA => hdrm_hba_rd_data,

            DPM_RD_CHAN => hdrm_data_rd_chan,
            DPM_RD_DATA => hdrm_dpm_rd_data,
            HPM_RD_CHAN => hdrm_hdr_rd_chan,
            HPM_RD_DATA => hdrm_hpm_rd_data);


    USER_RX_MFB_DST_RDY <= hdr_log_dst_rdy and data_path_dst_rdy;

    rx_dma_hdr_manager_i : entity work.RX_DMA_CALYPTE_HDR_MANAGER
        generic map (
            MFB_REGIONS   => USER_RX_MFB_REGIONS,
            CHANNELS      => CHANNELS,
            PKT_MTU       => PKT_SIZE_MAX,
            METADATA_SIZE => HDR_META_WIDTH,
            ADDR_WIDTH    => SW_ADDR_WIDTH,
            POINTER_WIDTH => POINTER_WIDTH,
            DEVICE        => DEVICE)
        port map (
            CLK   => CLK,
            RESET => RESET,

            START_REQ_CHANNEL => start_req_chan,
            START_REQ_VLD     => start_req_vld,
            START_REQ_DONE    => start_req_done,

            STOP_REQ_CHANNEL => stop_req_chan,
            STOP_REQ_VLD     => stop_req_vld,
            STOP_REQ_DONE    => stop_req_done,

            HDP_UPDATE_CHAN => hdrm_hdp_update_chan,
            HDP_UPDATE_DATA => hdrm_hdp_update_data,
            HDP_UPDATE_EN   => hdrm_hdp_update_en,
            HHP_UPDATE_CHAN => hdrm_hhp_update_chan,
            HHP_UPDATE_DATA => hdrm_hhp_update_data,
            HHP_UPDATE_EN   => hdrm_hhp_update_en,

            ADDR_DATA_CHANNEL    => hdrm_data_rd_chan,
            ADDR_DATA_BASE       => hdrm_dba_rd_data,
            ADDR_DATA_MASK       => hdrm_dpm_rd_data,
            ADDR_DATA_SW_POINTER => hdrm_sdp_rd_data,

            ADDR_HEADER_CHANNEL    => hdrm_hdr_rd_chan,
            ADDR_HEADER_BASE       => hdrm_hba_rd_data,
            ADDR_HEADER_MASK       => hdrm_hpm_rd_data,
            ADDR_HEADER_SW_POINTER => hdrm_shp_rd_data,

            INF_META     => USER_RX_MFB_META_HDR_META,
            INF_CHANNEL  => USER_RX_MFB_META_CHAN,
            INF_SRC_RDY  => USER_RX_MFB_SRC_RDY and data_path_dst_rdy and USER_RX_MFB_SOF(0),
            INF_DST_RDY  => hdr_log_dst_rdy,

            STAT_PKT_LNG => stat_frame_lng,
            MFB_EOF      => mfb_eof_lng_check,
            MFB_SRC_RDY  => mfb_src_rdy_lng_check,
            MFB_DST_RDY  => mfb_dst_rdy_lng_check,

            DMA_PCIE_HDR_SIZE    => hdrm_dma_pcie_hdr_size,
            DMA_PCIE_HDR         => hdrm_dma_pcie_hdr,
            DMA_PCIE_HDR_SRC_RDY => hdrm_dma_pcie_hdr_src_rdy,
            DMA_PCIE_HDR_DST_RDY => hdrm_dma_pcie_hdr_dst_rdy,

            DATA_PCIE_HDR_SIZE    => hdrm_data_pcie_hdr_size,
            DATA_PCIE_HDR         => hdrm_data_pcie_hdr,
            DATA_PCIE_HDR_SRC_RDY => hdrm_data_pcie_hdr_src_rdy,
            DATA_PCIE_HDR_DST_RDY => hdrm_data_pcie_hdr_dst_rdy,

            DMA_DISCARD     => hdrm_pkt_drop,
            DMA_HDR         => hdrm_dma_hdr_data,
            DMA_HDR_SRC_RDY => hdrm_dma_hdr_src_rdy,
            DMA_HDR_DST_RDY => hdrm_dma_hdr_dst_rdy,

            PKT_CNTR_CHAN     => hdrm_pkt_sent_chan,
            PKT_CNTR_SENT_INC => hdrm_pkt_sent_inc,
            PKT_CNTR_DISC_INC => hdrm_pkt_disc_inc,
            PKT_CNTR_PKT_SIZE => hdrm_pkt_sent_bytes);

    rx_dma_hdr_insertor_i : entity work.RX_DMA_CALYPTE_HDR_INSERTOR
        generic map (
            RX_REGION_SIZE => MFB_REGION_SIZE_TRBUF2INS,
            RX_BLOCK_SIZE  => MFB_BLOCK_SIZE_TRBUF2INS,
            RX_ITEM_WIDTH  => MFB_ITEM_WIDTH_TRBUF2INS,

            TX_REGIONS     => PCIE_UP_MFB_REGIONS,
            TX_REGION_SIZE => PCIE_UP_MFB_REGION_SIZE,
            TX_BLOCK_SIZE  => PCIE_UP_MFB_BLOCK_SIZE,
            TX_ITEM_WIDTH  => PCIE_UP_MFB_ITEM_WIDTH,

            DEVICE       => DEVICE
        )
        port map (
            CLK => CLK,
            RST => RESET,

            RX_MFB_DATA    => trbuf_fifo_tx_data,
            RX_MFB_SOF     => trbuf_fifo_tx_sof,
            RX_MFB_EOF     => trbuf_fifo_tx_eof,
            RX_MFB_SRC_RDY => trbuf_fifo_tx_src_rdy,
            RX_MFB_DST_RDY => trbuf_fifo_tx_dst_rdy,

            TX_MFB_DATA    => PCIE_UP_MFB_DATA,
            TX_MFB_META    => PCIE_UP_MFB_META,
            TX_MFB_SOF     => PCIE_UP_MFB_SOF,
            TX_MFB_EOF     => PCIE_UP_MFB_EOF,
            TX_MFB_SOF_POS => PCIE_UP_MFB_SOF_POS,
            TX_MFB_EOF_POS => PCIE_UP_MFB_EOF_POS,
            TX_MFB_SRC_RDY => PCIE_UP_MFB_SRC_RDY,
            TX_MFB_DST_RDY => PCIE_UP_MFB_DST_RDY,

            HDRM_DMA_PCIE_HDR_SIZE    => hdrm_dma_pcie_hdr_size,
            HDRM_DMA_PCIE_HDR         => hdrm_dma_pcie_hdr,
            HDRM_DMA_PCIE_HDR_SRC_RDY => hdrm_dma_pcie_hdr_src_rdy,
            HDRM_DMA_PCIE_HDR_DST_RDY => hdrm_dma_pcie_hdr_dst_rdy,

            HDRM_DATA_PCIE_HDR_SIZE    => hdrm_data_pcie_hdr_size,
            HDRM_DATA_PCIE_HDR         => hdrm_data_pcie_hdr,
            HDRM_DATA_PCIE_HDR_SRC_RDY => hdrm_data_pcie_hdr_src_rdy,
            HDRM_DATA_PCIE_HDR_DST_RDY => hdrm_data_pcie_hdr_dst_rdy,

            HDRM_PKT_DROP        => hdrm_pkt_drop,
            HDRM_DMA_HDR_DATA    => hdrm_dma_hdr_data,
            HDRM_DMA_HDR_SRC_RDY => hdrm_dma_hdr_src_rdy,
            HDRM_DMA_HDR_DST_RDY => hdrm_dma_hdr_dst_rdy);

    tr_buf_fifo_g: if (TRBUF_FIFO_EN) generate

        trbuf_fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS             => 1,
                REGION_SIZE         => MFB_REGION_SIZE_TRBUF2INS,
                BLOCK_SIZE          => MFB_BLOCK_SIZE_TRBUF2INS,
                ITEM_WIDTH          => MFB_ITEM_WIDTH_TRBUF2INS,
                META_WIDTH          => 0,
                FIFO_DEPTH          => 32,
                RAM_TYPE            => "AUTO",
                DEVICE              => DEVICE,
                ALMOST_FULL_OFFSET  => 2,
                ALMOST_EMPTY_OFFSET => 2)
            port map (
                CLK         => CLK,
                RST         => RESET,

                RX_DATA     => trbuf_fifo_rx_data,
                RX_META     => (others => '0'),
                RX_SOF_POS  => trbuf_fifo_rx_sof_pos,
                RX_EOF_POS  => trbuf_fifo_rx_eof_pos,
                RX_SOF(0)   => trbuf_fifo_rx_sof,
                RX_EOF(0)   => trbuf_fifo_rx_eof,
                RX_SRC_RDY  => trbuf_fifo_rx_src_rdy,
                RX_DST_RDY  => trbuf_fifo_rx_dst_rdy,

                TX_DATA     => trbuf_fifo_tx_data,
                TX_META     => open,
                TX_SOF_POS  => trbuf_fifo_tx_sof_pos,
                TX_EOF_POS  => trbuf_fifo_tx_eof_pos,
                TX_SOF(0)   => trbuf_fifo_tx_sof,
                TX_EOF(0)   => trbuf_fifo_tx_eof,
                TX_SRC_RDY  => trbuf_fifo_tx_src_rdy,
                TX_DST_RDY  => trbuf_fifo_tx_dst_rdy,

                FIFO_STATUS => open,

                FIFO_AFULL  => open,
                FIFO_AEMPTY => open);

    else generate

        trbuf_fifo_tx_data    <= trbuf_fifo_rx_data;
        trbuf_fifo_tx_sof_pos <= trbuf_fifo_rx_sof_pos;
        trbuf_fifo_tx_eof_pos <= trbuf_fifo_rx_eof_pos;
        trbuf_fifo_tx_sof     <= trbuf_fifo_rx_sof;
        trbuf_fifo_tx_eof     <= trbuf_fifo_rx_eof;
        trbuf_fifo_tx_src_rdy <= trbuf_fifo_rx_src_rdy;
        trbuf_fifo_rx_dst_rdy <= trbuf_fifo_tx_dst_rdy;

    end generate;

    tr_buff_g : if (BUFFERED_DATA_SIZE = MFB_REGION_SIZE_INBUF2TRBUF*MFB_BLOCK_SIZE_INBUF2TRBUF) generate

        trbuf_fifo_rx_data      <= mfb_data_inbuf;
        trbuf_fifo_rx_sof       <= mfb_sof_inbuf;
        trbuf_fifo_rx_eof       <= mfb_eof_inbuf;
        trbuf_fifo_rx_src_rdy   <= mfb_src_rdy_inbuf;
        mfb_dst_rdy_inbuf <= trbuf_fifo_rx_dst_rdy;

    else generate

        transaction_buffer_i : entity work.RX_DMA_CALYPTE_TRANS_BUFFER
            generic map (
                RX_REGION_SIZE => MFB_REGION_SIZE_INBUF2TRBUF,
                RX_BLOCK_SIZE  => MFB_BLOCK_SIZE_INBUF2TRBUF,
                RX_ITEM_WIDTH  => MFB_ITEM_WIDTH_INBUF2TRBUF,

                BUFFERED_DATA_SIZE => BUFFERED_DATA_SIZE,
                REG_OUT_EN         => TRBUF_REG_EN)
            port map (
                CLK => CLK,
                RST => RESET,

                RX_MFB_DATA    => mfb_data_lng_check,
                RX_MFB_EOF_POS => mfb_eof_pos_lng_check,
                RX_MFB_SOF     => mfb_sof_lng_check(0),
                RX_MFB_EOF     => mfb_eof_lng_check(0),
                RX_MFB_SRC_RDY => mfb_src_rdy_lng_check,
                RX_MFB_DST_RDY => mfb_dst_rdy_lng_check,

                TX_MFB_DATA    => trbuf_fifo_rx_data,
                TX_MFB_SOF_POS => trbuf_fifo_rx_sof_pos,
                TX_MFB_EOF_POS => trbuf_fifo_rx_eof_pos,
                TX_MFB_SOF     => trbuf_fifo_rx_sof,
                TX_MFB_EOF     => trbuf_fifo_rx_eof,
                TX_MFB_SRC_RDY => trbuf_fifo_rx_src_rdy,
                TX_MFB_DST_RDY => trbuf_fifo_rx_dst_rdy);

    end generate;

    mfb_frame_lng_check_i : entity work.MFB_FRAME_LNG_CHECK
        generic map (
            REGIONS     => USER_RX_MFB_REGIONS,
            REGION_SIZE => USER_RX_MFB_REGION_SIZE,
            BLOCK_SIZE  => USER_RX_MFB_BLOCK_SIZE,
            ITEM_WIDTH  => USER_RX_MFB_ITEM_WIDTH,

            META_WIDTH  => 0,
            LNG_WIDTH   => log2(PKT_SIZE_MAX+1),
            REG_BITMAP  => "0000")
        port map (
            CLK            => CLK,
            RESET          => RESET,

            FRAME_LNG_MAX  => std_logic_vector(to_unsigned(PKT_SIZE_MAX, log2(PKT_SIZE_MAX+1))),
            FRAME_LNG_MIN  => std_logic_vector(to_unsigned(60,           log2(PKT_SIZE_MAX+1))),

            RX_DATA        => mfb_data_inbuf,
            RX_META        => (others => '0'),
            RX_SOF(0)      => mfb_sof_inbuf,
            RX_EOF(0)      => mfb_eof_inbuf,
            RX_SOF_POS     => mfb_sof_pos_inbuf,
            RX_EOF_POS     => mfb_eof_pos_inbuf,
            RX_SRC_RDY     => mfb_src_rdy_inbuf,
            RX_DST_RDY     => mfb_dst_rdy_inbuf,

            TX_DATA        => mfb_data_lng_check,
            TX_META        => open,
            TX_SOF         => open,
            TX_EOF         => mfb_eof_lng_check,
            TX_SOF_POS     => open,
            TX_EOF_POS     => mfb_eof_pos_lng_check,
            TX_SRC_RDY     => mfb_src_rdy_lng_check,
            TX_DST_RDY     => mfb_dst_rdy_lng_check,

            -- an error of maximum packet length does not make sense since
            -- packet beyond this length are not supported by the design
            TX_LNG_MAX_ERR => stat_frame_lng_max_err,
            TX_LNG_MIN_ERR => stat_frame_lng_min_err,
            TX_LNG_OVF_ERR => stat_frame_lng_ovf_err,
            TX_FRAME_LNG   => stat_frame_lng);

    input_buffer_i : entity work.RX_DMA_CALYPTE_INPUT_BUFFER
        generic map (
            REGION_SIZE => USER_RX_MFB_REGION_SIZE,
            BLOCK_SIZE  => USER_RX_MFB_BLOCK_SIZE,
            ITEM_WIDTH  => USER_RX_MFB_ITEM_WIDTH)
        port map (
            CLK => CLK,
            RST => RESET,

            RX_MFB_DATA    => USER_RX_MFB_DATA,
            RX_MFB_SOF_POS => USER_RX_MFB_SOF_POS,
            RX_MFB_EOF_POS => USER_RX_MFB_EOF_POS,
            RX_MFB_SOF     => USER_RX_MFB_SOF(0),
            RX_MFB_EOF     => USER_RX_MFB_EOF(0),
            RX_MFB_SRC_RDY => USER_RX_MFB_SRC_RDY and hdr_log_dst_rdy,
            RX_MFB_DST_RDY => data_path_dst_rdy,

            TX_MFB_DATA    => mfb_data_inbuf,
            TX_MFB_SOF_POS => mfb_sof_pos_inbuf,
            TX_MFB_EOF_POS => mfb_eof_pos_inbuf,
            TX_MFB_SOF     => mfb_sof_inbuf,
            TX_MFB_EOF     => mfb_eof_inbuf,
            TX_MFB_SRC_RDY => mfb_src_rdy_inbuf,
            TX_MFB_DST_RDY => mfb_dst_rdy_inbuf);

end architecture;
