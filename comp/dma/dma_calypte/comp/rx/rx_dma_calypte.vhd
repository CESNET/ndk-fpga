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

        MI_WIDTH : natural := 32;

        -- User Logic MFB configuration
        USER_RX_MFB_REGIONS     : natural := 1;
        USER_RX_MFB_REGION_SIZE : natural := 8;
        USER_RX_MFB_BLOCK_SIZE  : natural := 8;
        USER_RX_MFB_ITEM_WIDTH  : natural := 8;

        -- PCIe MFB configuration (Requester Request interface)
        PCIE_UP_MFB_REGIONS     : natural := 2;
        PCIE_UP_MFB_REGION_SIZE : natural := 1;
        PCIE_UP_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_UP_MFB_ITEM_WIDTH  : natural := 32;

        -- Total number of DMA Channels, each with its separate buffers in the host memory.
        CHANNELS       : natural := 8;
        -- * Width of Software and Hardware Descriptor/Header Pointer
        -- * Defines width of signals used for these values in DMA Module
        -- * Affects logic complexity
        -- * Maximum value: 32 (restricted by size of pointer MI registers)
        POINTER_WIDTH  : natural := 16;
        -- Width of RAM address
        SW_ADDR_WIDTH  : natural := 64;
        -- Actual width of packet and byte counters
        CNTRS_WIDTH    : natural := 64;
        -- Width of application metadata transported within the DMA headers.
        -- In bits.
        HDR_META_WIDTH : natural := 24;
        -- * Maximum size of a packet in bytes.
        -- * Defines width of Packet length signals.
        -- * Maximum allowed value is 2**16 - 1
        PKT_SIZE_MAX   : natural := 2**16 - 1;
        -- Enables a register in the transaction buffer that improves throughput (but increases
        -- latency by one clock period).
        TRBUF_REG_EN   : boolean := FALSE;
        -- Enables performance counters in the design for metrics.
        PERF_CNTR_EN   : boolean := FALSE
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

        -- =========================================================================================
        -- Pointer update interface
        -- =========================================================================================
        PTR_UPD_BUFF_BA  : out std_logic_vector(SW_ADDR_WIDTH -1 downto 0);
        PTR_UPD_P2P_EN   : out std_logic;
        PTR_UPD_HDP      : out std_logic_vector(POINTER_WIDTH -1 downto 0);
        PTR_UPD_HHP      : out std_logic_vector(POINTER_WIDTH -1 downto 0);
        PTR_UPD_DISP_EN  : out std_logic;
        PTR_UPD_DISP_ACK : in  std_logic;

        -- =========================================================================================================
        -- User MFB interface
        --
        -- Receives packets from the application logic
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

        --=========================================================================================================
        -- (PCIe Requester Request) MFB interface
        --
        -- Dispatches packets to the PCIe domain
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

    constant IS_INTEL_DEV    : boolean := (DEVICE = "STRATIX10" or DEVICE = "AGILEX");

    constant MI_SPLIT_PORTS : natural := 2;
    constant MI_SPLIT_BASES : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH-1 downto 0) := (
        0 => X"00000000",
        1 => X"00003000");

    constant MI_SPLIT_ADDR_MASK : std_logic_vector(MI_WIDTH-1 downto 0) := X"00003000";

    signal mi_split_dwr  : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_addr : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_be   : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH/8 -1 downto 0);
    signal mi_split_rd   : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_wr   : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_drd  : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_ardy : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_drdy : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);

    -- =============================================================================================
    -- SW Manager ---> Header Manager
    -- =============================================================================================
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

    signal hdrm_dma_pcie_hdr         : std_logic_vector (127 downto 0);
    signal hdrm_dma_pcie_hdr_src_rdy : std_logic;
    signal hdrm_dma_pcie_hdr_dst_rdy : std_logic;

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

    -- =============================================================================================
    -- Transaction Buffer ---> Header Insertor
    -- =============================================================================================
    signal mfb_data_trbuf    : std_logic_vector(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS*MFB_ITEM_WIDTH_TRBUF2INS-1 downto 0);
    signal mfb_eof_pos_trbuf : std_logic_vector (max(1, log2(MFB_REGION_SIZE_TRBUF2INS*MFB_BLOCK_SIZE_TRBUF2INS))-1 downto 0);
    signal mfb_sof_trbuf     : std_logic;
    signal mfb_eof_trbuf     : std_logic;
    signal mfb_src_rdy_trbuf : std_logic;
    signal mfb_dst_rdy_trbuf : std_logic;

    -- =============================================================================================
    -- Frame length checker ---> Transaction buffer
    -- =============================================================================================
    signal mfb_data_lng_check    : std_logic_vector(MFB_REGION_SIZE_INBUF2TRBUF*MFB_BLOCK_SIZE_INBUF2TRBUF*MFB_ITEM_WIDTH_INBUF2TRBUF-1 downto 0);
    signal mfb_sof_lng_check     : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal mfb_eof_lng_check     : std_logic_vector(USER_RX_MFB_REGIONS -1 downto 0);
    signal mfb_eof_pos_lng_check : std_logic_vector(max(1, log2(MFB_REGION_SIZE_INBUF2TRBUF*MFB_BLOCK_SIZE_INBUF2TRBUF))-1 downto 0);
    signal mfb_src_rdy_lng_check : std_logic;
    signal mfb_dst_rdy_lng_check : std_logic;

    signal stat_frame_lng         : std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);
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

    -- =============================================================================================
    -- Performance counters' increment signals
    -- =============================================================================================
    constant PERF_CNTR_NUM   : positive := 6;
    constant PERF_CNTR_WIDTH : positive := 64;

    signal perf_cntr_diff_packed : slv_array_t(PERF_CNTR_NUM -1 downto 0)(PERF_CNTR_WIDTH -1 downto 0);
    signal perf_cntr_incr_packed : std_logic_vector(PERF_CNTR_NUM -1 downto 0);

    signal data_addr_req_cntr_incr    : std_logic;
    signal dma_hdr_addr_req_cntr_incr : std_logic;
    signal data_addr_stall_incr       : std_logic;
    signal dma_hdr_addr_stall_incr    : std_logic;
    signal pcie_mfb_stall_incr        : std_logic;
    signal pcie_mfb_beats_incr        : std_logic;

    signal data_buff_full_chan         : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal data_buff_full_cntr_incr    : std_logic;
    signal dma_hdr_buff_full_chan      : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal dma_hdr_buff_full_cntr_incr : std_logic;

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

    -- attribute mark_debug of mfb_data_trbuf    : signal is "true";
    -- attribute mark_debug of mfb_sof_trbuf     : signal is "true";
    -- attribute mark_debug of mfb_eof_trbuf     : signal is "true";
    -- attribute mark_debug of mfb_sof_pos_trbuf : signal is "true";
    -- attribute mark_debug of mfb_eof_pos_trbuf : signal is "true";
    -- attribute mark_debug of mfb_src_rdy_trbuf : signal is "true";
    -- attribute mark_debug of mfb_dst_rdy_trbuf : signal is "true";

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

    perf_cntr_g: if (PERF_CNTR_EN) generate

        mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map (
            ADDR_WIDTH => MI_WIDTH,
            DATA_WIDTH => MI_WIDTH,
            META_WIDTH => 0,
            PORTS      => MI_SPLIT_PORTS,
            PIPE_OUT   => (others => FALSE),

            ADDR_BASES => MI_SPLIT_PORTS,
            ADDR_BASE  => MI_SPLIT_BASES,
            ADDR_MASK  => MI_SPLIT_ADDR_MASK,

            DEVICE => DEVICE
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_DWR  => MI_DWR,
            RX_MWR  => (others => '0'),
            RX_ADDR => MI_ADDR,
            RX_BE   => MI_BE,
            RX_RD   => MI_RD,
            RX_WR   => MI_WR,
            RX_ARDY => MI_ARDY,
            RX_DRD  => MI_DRD,
            RX_DRDY => MI_DRDY,

            TX_DWR  => mi_split_dwr,
            TX_MWR  => open,
            TX_ADDR => mi_split_addr,
            TX_BE   => mi_split_be,
            TX_RD   => mi_split_rd,
            TX_WR   => mi_split_wr,
            TX_ARDY => mi_split_ardy,
            TX_DRD  => mi_split_drd,
            TX_DRDY => mi_split_drdy
        );

        perf_counters_p: entity work.DATA_LOGGER
        generic map (
            MI_DATA_WIDTH   => MI_WIDTH,
            MI_ADDR_WIDTH   => MI_WIDTH,

            CNTER_CNT       => PERF_CNTR_NUM,
            VALUE_CNT       => 2,

            CTRLO_WIDTH     => 0,
            CTRLI_WIDTH     => 0,

            CNTER_WIDTH     => PERF_CNTR_WIDTH,
            VALUE_WIDTH     => (others => log2(CHANNELS)),

            MIN_EN          => (others => FALSE),
            MAX_EN          => (others => FALSE),
            SUM_EN          => (others => TRUE),
            HIST_EN         => (others => TRUE),

            SUM_EXTRA_WIDTH => (others => 16),
            HIST_BOX_CNT    => (others => CHANNELS),
            HIST_BOX_WIDTH  => (others => PERF_CNTR_WIDTH),
            CTRLO_DEFAULT   => (others => '0')
        )
        port map (
            CLK           => CLK,
            RST           => RESET,

            RST_DONE      => open,
            SW_RST        => open,

            CTRLO         => open,
            CTRLI         => (others => '0'),

            CNTERS_INCR   => perf_cntr_incr_packed,
            CNTERS_SUBMIT => perf_cntr_incr_packed,
            CNTERS_DIFF   => perf_cntr_diff_packed,

            VALUES_VLD    => data_buff_full_cntr_incr & dma_hdr_buff_full_cntr_incr,
            VALUES        => data_buff_full_chan & dma_hdr_buff_full_chan,

            MI_DWR        => mi_split_dwr(1),
            MI_ADDR       => mi_split_addr(1),
            MI_BE         => mi_split_be(1),
            MI_RD         => mi_split_rd(1),
            MI_WR         => mi_split_wr(1),
            MI_ARDY       => mi_split_ardy(1),
            MI_DRD        => mi_split_drd(1),
            MI_DRDY       => mi_split_drdy(1)
        );

        perf_cntr_diff_packed <= (others => std_logic_vector(to_unsigned(1, PERF_CNTR_WIDTH)));
        perf_cntr_incr_packed <= pcie_mfb_beats_incr
                                 & data_addr_req_cntr_incr
                                 & dma_hdr_addr_req_cntr_incr
                                 & data_addr_stall_incr
                                 & dma_hdr_addr_stall_incr
                                 & pcie_mfb_stall_incr;

        -- Counts the amount of beats where a transaction is ready but the PCIE interface is not
        pcie_mfb_stall_incr <= (not PCIE_UP_MFB_DST_RDY) and PCIE_UP_MFB_SRC_RDY and (not RESET);
        -- Counts an overall amount of beats in which packets are sent
        pcie_mfb_beats_incr <= PCIE_UP_MFB_DST_RDY and PCIE_UP_MFB_SRC_RDY and (not RESET);
    else generate
        mi_split_dwr(0)     <= MI_DWR;
        mi_split_addr(0)    <= MI_ADDR;
        mi_split_be(0)      <= MI_BE;
        mi_split_rd(0)      <= MI_RD;
        mi_split_wr(0)      <= MI_WR;

        MI_ARDY <= mi_split_ardy(0);
        MI_DRD  <= mi_split_drd(0);
        MI_DRDY <= mi_split_drdy(0);
    end generate;

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
        MI_WIDTH           => MI_WIDTH
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        MI_ADDR => mi_split_addr(0),
        MI_DWR  => mi_split_dwr(0),
        MI_BE   => mi_split_be(0),
        MI_RD   => mi_split_rd(0),
        MI_WR   => mi_split_wr(0),
        MI_DRD  => mi_split_drd(0),
        MI_ARDY => mi_split_ardy(0),
        MI_DRDY => mi_split_drdy(0),

        PKT_SENT_CHAN     => hdrm_pkt_sent_chan,
        PKT_SENT_INC      => hdrm_pkt_sent_inc,
        PKT_SENT_BYTES    => hdrm_pkt_sent_bytes,
        PKT_DISCARD_CHAN  => hdrm_pkt_sent_chan,
        PKT_DISCARD_INC   => hdrm_pkt_disc_inc,
        PKT_DISCARD_BYTES => hdrm_pkt_sent_bytes,

        START_REQ_CHAN => start_req_chan,
        START_REQ_VLD  => start_req_vld,
        START_REQ_ACK  => start_req_done,

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
        HPM_RD_DATA => hdrm_hpm_rd_data,

        PTR_UPD_BUFF_BA  => PTR_UPD_BUFF_BA,
        PTR_UPD_P2P_EN   => PTR_UPD_P2P_EN,
        PTR_UPD_HDP      => PTR_UPD_HDP,
        PTR_UPD_HHP      => PTR_UPD_HHP,
        PTR_UPD_DISP_EN  => PTR_UPD_DISP_EN,
        PTR_UPD_DISP_ACK => PTR_UPD_DISP_ACK,

        DATA_BUFF_FULL_CHAN         => data_buff_full_chan,
        DATA_BUFF_FULL_CNTR_INCR    => data_buff_full_cntr_incr,
        DMA_HDR_BUFF_FULL_CHAN      => dma_hdr_buff_full_chan,
        DMA_HDR_BUFF_FULL_CNTR_INCR => dma_hdr_buff_full_cntr_incr
    );

    USER_RX_MFB_DST_RDY <= hdr_log_dst_rdy and data_path_dst_rdy;

    rx_dma_hdr_manager_i : entity work.RX_DMA_CALYPTE_HDR_MANAGER
    generic map (
        MFB_REGIONS   => USER_RX_MFB_REGIONS,
        CHANNELS      => CHANNELS,
        PKT_MTU       => PKT_SIZE_MAX,
        METADATA_SIZE => HDR_META_WIDTH,
        ADDR_WIDTH    => SW_ADDR_WIDTH,
        POINTER_WIDTH => POINTER_WIDTH,
        DEVICE        => DEVICE
    )
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

        DMA_PCIE_HDR         => hdrm_dma_pcie_hdr,
        DMA_PCIE_HDR_SRC_RDY => hdrm_dma_pcie_hdr_src_rdy,
        DMA_PCIE_HDR_DST_RDY => hdrm_dma_pcie_hdr_dst_rdy,

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
        PKT_CNTR_PKT_SIZE => hdrm_pkt_sent_bytes,

        DATA_ADDR_REQ_CNTR_INC    => data_addr_req_cntr_incr,
        DMA_HDR_ADDR_REQ_CNTR_INC => dma_hdr_addr_req_cntr_incr,
        DATA_ADDR_STALL_INC       => data_addr_stall_incr,
        DMA_HDR_ADDR_STALL_INC    => dma_hdr_addr_stall_incr
    );


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

        RX_MFB_DATA    => mfb_data_trbuf,
        RX_MFB_SOF     => mfb_sof_trbuf,
        RX_MFB_EOF     => mfb_eof_trbuf,
        RX_MFB_EOF_POS => mfb_eof_pos_trbuf,
        RX_MFB_SRC_RDY => mfb_src_rdy_trbuf,
        RX_MFB_DST_RDY => mfb_dst_rdy_trbuf,

        TX_MFB_DATA    => PCIE_UP_MFB_DATA,
        TX_MFB_META    => PCIE_UP_MFB_META,
        TX_MFB_SOF     => PCIE_UP_MFB_SOF,
        TX_MFB_EOF     => PCIE_UP_MFB_EOF,
        TX_MFB_SOF_POS => PCIE_UP_MFB_SOF_POS,
        TX_MFB_EOF_POS => PCIE_UP_MFB_EOF_POS,
        TX_MFB_SRC_RDY => PCIE_UP_MFB_SRC_RDY,
        TX_MFB_DST_RDY => PCIE_UP_MFB_DST_RDY,

        HDRM_DMA_PCIE_HDR         => hdrm_dma_pcie_hdr,
        HDRM_DMA_PCIE_HDR_SRC_RDY => hdrm_dma_pcie_hdr_src_rdy,
        HDRM_DMA_PCIE_HDR_DST_RDY => hdrm_dma_pcie_hdr_dst_rdy,

        HDRM_DATA_PCIE_HDR         => hdrm_data_pcie_hdr,
        HDRM_DATA_PCIE_HDR_SRC_RDY => hdrm_data_pcie_hdr_src_rdy,
        HDRM_DATA_PCIE_HDR_DST_RDY => hdrm_data_pcie_hdr_dst_rdy,

        HDRM_PKT_DROP        => hdrm_pkt_drop,
        HDRM_DMA_HDR_DATA    => hdrm_dma_hdr_data,
        HDRM_DMA_HDR_SRC_RDY => hdrm_dma_hdr_src_rdy,
        HDRM_DMA_HDR_DST_RDY => hdrm_dma_hdr_dst_rdy
    );

    transaction_buffer_i : entity work.RX_DMA_CALYPTE_TRANS_BUFFER
    generic map (
        RX_REGION_SIZE => MFB_REGION_SIZE_INBUF2TRBUF,
        RX_BLOCK_SIZE  => MFB_BLOCK_SIZE_INBUF2TRBUF,
        RX_ITEM_WIDTH  => MFB_ITEM_WIDTH_INBUF2TRBUF,

        BUFFERED_DATA_SIZE => BUFFERED_DATA_SIZE,
        REG_OUT_EN         => TRBUF_REG_EN
    )
    port map (
        CLK => CLK,
        RST => RESET,

        RX_MFB_DATA    => mfb_data_lng_check,
        RX_MFB_EOF_POS => mfb_eof_pos_lng_check,
        RX_MFB_SOF     => mfb_sof_lng_check(0),
        RX_MFB_EOF     => mfb_eof_lng_check(0),
        RX_MFB_SRC_RDY => mfb_src_rdy_lng_check,
        RX_MFB_DST_RDY => mfb_dst_rdy_lng_check,

        TX_MFB_DATA    => mfb_data_trbuf,
        TX_MFB_SOF_POS => open,
        TX_MFB_EOF_POS => mfb_eof_pos_trbuf,
        TX_MFB_SOF     => mfb_sof_trbuf,
        TX_MFB_EOF     => mfb_eof_trbuf,
        TX_MFB_SRC_RDY => mfb_src_rdy_trbuf,
        TX_MFB_DST_RDY => mfb_dst_rdy_trbuf
    );

    -- The counter of packet length that is provided to the HDR_MANAGER in order to generate
    -- a correct amount of PCIe headers  for the data transactions.
    mfb_frame_lng_check_i : entity work.MFB_FRAME_LNG_CHECK
    generic map (
        REGIONS     => USER_RX_MFB_REGIONS,
        REGION_SIZE => USER_RX_MFB_REGION_SIZE,
        BLOCK_SIZE  => USER_RX_MFB_BLOCK_SIZE,
        ITEM_WIDTH  => USER_RX_MFB_ITEM_WIDTH,

        META_WIDTH  => 0,
        LNG_WIDTH   => log2(PKT_SIZE_MAX+1),
        REG_BITMAP  => tsel(IS_INTEL_DEV, "1111", "0000")
    )
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
        TX_FRAME_LNG   => stat_frame_lng
    );

    input_buffer_i : entity work.RX_DMA_CALYPTE_INPUT_BUFFER
    generic map (
        REGION_SIZE => USER_RX_MFB_REGION_SIZE,
        BLOCK_SIZE  => USER_RX_MFB_BLOCK_SIZE,
        ITEM_WIDTH  => USER_RX_MFB_ITEM_WIDTH
    )
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
        TX_MFB_DST_RDY => mfb_dst_rdy_inbuf
    );

end architecture;
