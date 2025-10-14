-- dma_calypte.vhd: encapsulates RX and TX of the Calypte DMA controller
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity DMA_CALYPTE is
    generic (
        -- ==========================================================================================
        -- Global settings
        --
        -- Settings affecting both RX and TX or the top level entity itself
        -- ==========================================================================================
        -- Name of target device, the supported are:
        --
        -- * "ULTRASCALE"
        -- * "STRATIX10"
        -- * "AGILEX"
        DEVICE : string := "ULTRASCALE";

        -- USER MFB interface configuration that is used for user data stream. The alowed
        -- configurations are:
        --
        -- * (1,4,8,8)
        -- * (1,8,8,8)
        USR_MFB_REGIONS     : natural := 1;
        USR_MFB_REGION_SIZE : natural := 8;
        USR_MFB_BLOCK_SIZE  : natural := 8;
        USR_MFB_ITEM_WIDTH  : natural := 8;

        -- Width of User Header Metadata information
        --
        -- * on RX: added to the DMA header
        -- * on TX: extracted from a DMA header
        HDR_META_WIDTH : natural := 24;

        -- ==========================================================================================
        -- Requester Request (RQ) MFB interface settings. The allowed configurations are:
        --
        -- * (1,1,8,32)
        -- * (2,1,8,32)
        -- ==========================================================================================
        PCIE_RQ_MFB_REGIONS     : natural := 2;
        PCIE_RQ_MFB_REGION_SIZE : natural := 1;
        PCIE_RQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RQ_MFB_ITEM_WIDTH  : natural := 32;

        -- =========================================================================================
        -- Completer Request (CQ) MFB interface settings. The allowed configurations are:
        --
        -- * (1,1,8,32)
        -- * (2,1,8,32)
        -- =========================================================================================
        PCIE_CQ_MFB_REGIONS     : natural := 2;
        PCIE_CQ_MFB_REGION_SIZE : natural := 1;
        PCIE_CQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CQ_MFB_ITEM_WIDTH  : natural := 32;

        -- ==========================================================================================
        -- RX DMA controller settings
        -- ==========================================================================================
        -- Total number of RX DMA Channels (powers of 2, starting at 2)
        RX_CHANNELS         : natural := 8;
        -- * Width of Software and Hardware Header/DataPointer.
        -- * Affects logic complexity (MI C/S registers especially)
        -- * Maximum value: 16
        RX_PTR_WIDTH        : natural := 16;
        -- Maximum size of a User packet in bytes (in interval between 60 and  2**12, inclusively)
        USR_RX_PKT_SIZE_MAX : natural := 2**12;
        -- Enables an additional register of the transaction buffer that improves
        -- throughput (see :ref:`rx_dma_calypte_trans_buffer`)
        TRBUF_REG_EN        : boolean := false;
        -- Enables performance counters alowing metrics generation.
        PERF_CNTR_EN        : boolean := false;

        -- =========================================================================================
        -- TX DMA controller settings
        -- =========================================================================================
        -- Total number of TX DMA Channels (powers of 2, starting at 2)
        TX_CHANNELS         : natural := 8;
        -- * Width of the Hardware Descriptor Pointer
        -- * Significantly affects the complexity of the controller (the C/S registers as well as
        --   buffers to store packets within each channel).
        -- * Maximum value: 13 (restricted as a compromise between the size of a controller and
        --   maximum intact size of a packet that the software can dispatch)
        TX_PTR_WIDTH        : natural := 13;
        -- Maximum size of a User packet in bytes (in an interval between 60 and 2**12, inclusively)
        USR_TX_PKT_SIZE_MAX : natural := 2**12;

        -- =========================================================================================
        -- Optional settings
        --
        -- Settings for testing and debugging, usually left at default values..
        -- =========================================================================================
        -- Width of statistical counters within each channel
        DSP_CNT_WIDTH      : natural := 64;
        -- Allows to disable one of the controllers in the DMA module
        RX_GEN_EN          : boolean := TRUE;
        TX_GEN_EN          : boolean := TRUE;
        -- Width of the debug signal, do not use unless you know what you are doing
        ST_SP_DBG_SIGNAL_W : natural := 4;
        -- Width of MI bus
        MI_WIDTH           : natural := 32
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- RX DMA User-side MFB
        -- =========================================================================================
        USR_RX_MFB_META_CHAN     : in std_logic_vector(log2(RX_CHANNELS) -1 downto 0);
        USR_RX_MFB_META_HDR_META : in std_logic_vector(HDR_META_WIDTH -1 downto 0);

        USR_RX_MFB_DATA    : in  std_logic_vector(USR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
        USR_RX_MFB_SOF     : in  std_logic_vector(USR_MFB_REGIONS -1 downto 0);
        USR_RX_MFB_EOF     : in  std_logic_vector(USR_MFB_REGIONS -1 downto 0);
        USR_RX_MFB_SOF_POS : in  std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
        USR_RX_MFB_EOF_POS : in  std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
        USR_RX_MFB_SRC_RDY : in  std_logic;
        USR_RX_MFB_DST_RDY : out std_logic := '1';

        -- =========================================================================================
        -- TX DMA User-side MFB
        -- =========================================================================================
        USR_TX_MFB_META_PKT_SIZE : out std_logic_vector(log2(USR_TX_PKT_SIZE_MAX + 1) -1 downto 0) := (others => '0');
        USR_TX_MFB_META_CHAN     : out std_logic_vector(log2(TX_CHANNELS) -1 downto 0)             := (others => '0');
        USR_TX_MFB_META_HDR_META : out std_logic_vector(HDR_META_WIDTH -1 downto 0)                := (others => '0');

        USR_TX_MFB_DATA    : out std_logic_vector(USR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0) := (others => '0');
        USR_TX_MFB_SOF     : out std_logic_vector(USR_MFB_REGIONS -1 downto 0)                                                          := (others => '0');
        USR_TX_MFB_EOF     : out std_logic_vector(USR_MFB_REGIONS -1 downto 0)                                                          := (others => '0');
        USR_TX_MFB_SOF_POS : out std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0)                        := (others => '0');
        USR_TX_MFB_EOF_POS : out std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0)     := (others => '0');
        USR_TX_MFB_SRC_RDY : out std_logic                                                                                              := '0';
        USR_TX_MFB_DST_RDY : in  std_logic;

        -- =========================================================================================
        -- Debug signals
        --
        -- Should not be used by the user of the component
        -- =========================================================================================
        ST_SP_DBG_CHAN : out std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
        ST_SP_DBG_META : out std_logic_vector(ST_SP_DBG_SIGNAL_W -1 downto 0);

        -- =========================================================================================
        -- RQ PCIe interface
        --
        -- Upstream MFB interface (for sending data to the PCIe Endpoint)
        -- =========================================================================================
        PCIE_RQ_MFB_DATA    : out std_logic_vector(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_RQ_MFB_META    : out std_logic_vector(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
        PCIE_RQ_MFB_SOF     : out std_logic_vector(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_EOF     : out std_logic_vector(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_SOF_POS : out std_logic_vector(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_EOF_POS : out std_logic_vector(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_SRC_RDY : out std_logic;
        PCIE_RQ_MFB_DST_RDY : in  std_logic;

        -- =========================================================================================
        -- CQ PCIe interface
        --
        -- Downstream MFB interface (for receiving data from the PCIe Endpoint)
        -- =========================================================================================
        PCIE_CQ_MFB_DATA    : in  std_logic_vector(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_CQ_MFB_META    : in  std_logic_vector(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
        PCIE_CQ_MFB_SOF     : in  std_logic_vector(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_EOF     : in  std_logic_vector(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_SOF_POS : in  std_logic_vector(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_EOF_POS : in  std_logic_vector(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_SRC_RDY : in  std_logic;
        PCIE_CQ_MFB_DST_RDY : out std_logic := '1';

        -- ==========================================================================================
        -- MI interface for SW access
        -- ==========================================================================================
        MI_ADDR : in  std_logic_vector (MI_WIDTH -1 downto 0);
        MI_DWR  : in  std_logic_vector (MI_WIDTH -1 downto 0);
        MI_BE   : in  std_logic_vector (MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector (MI_WIDTH -1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
    );

end entity;

architecture FULL of DMA_CALYPTE is
    constant SW_ADDR_WIDTH : positive := 64;

    -- Address space mapping between the controllers
    constant MI_SPLIT_BASES : slv_array_t(2 -1 downto 0)(MI_WIDTH-1 downto 0) := (
        -- RX DMA
        0 => X"00000000",
        -- TX DMA
        1 => X"00200000");

    signal mi_split_dwr  : slv_array_t(2 -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_addr : slv_array_t(2 -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_be   : slv_array_t(2 -1 downto 0)(MI_WIDTH/8 -1 downto 0);
    signal mi_split_rd   : std_logic_vector(2 -1 downto 0);
    signal mi_split_wr   : std_logic_vector(2 -1 downto 0);
    signal mi_split_drd  : slv_array_t(2 -1 downto 0)(MI_WIDTH -1 downto 0);
    signal mi_split_ardy : std_logic_vector(2 -1 downto 0);
    signal mi_split_drdy : std_logic_vector(2 -1 downto 0);

    -- =============================================================================================
    -- Interfaces to Pointer Updater
    -- =============================================================================================
    signal rx_stop_req_buff_ba : std_logic_vector(SW_ADDR_WIDTH -1 downto 0);
    signal rx_stop_req_p2p_en  : std_logic;
    signal rx_stop_req_hdp     : std_logic_vector(RX_PTR_WIDTH -1 downto 0);
    signal rx_stop_req_hhp     : std_logic_vector(RX_PTR_WIDTH -1 downto 0);
    signal rx_stop_req_en      : std_logic;
    signal rx_stop_req_ack     : std_logic;

    signal tx_rt_upd_ch      : std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
    signal tx_rt_upd_buff_ba : std_logic_vector(63 downto 0);
    signal tx_rt_upd_p2p_en  : std_logic;

    signal tx_pkt_disp_upd_ch  : std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
    signal tx_pkt_disp_upd_hdp : std_logic_vector(TX_PTR_WIDTH -1 downto 0);
    signal tx_pkt_disp_upd_hhp : std_logic_vector(TX_PTR_WIDTH-3 -1 downto 0);
    signal tx_pkt_disp_upd_en  : std_logic;

    signal tx_start_req_ch  : std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
    signal tx_start_req_vld : std_logic;
    signal tx_start_req_ack : std_logic;

    signal tx_stop_req_buff_ba : std_logic_vector(SW_ADDR_WIDTH -1 downto 0);
    signal tx_stop_req_p2p_en  : std_logic;
    signal tx_stop_req_hdp     : std_logic_vector(TX_PTR_WIDTH -1 downto 0);
    signal tx_stop_req_hhp     : std_logic_vector(TX_PTR_WIDTH-3 -1 downto 0);
    signal tx_stop_req_en      : std_logic;
    signal tx_stop_req_ack     : std_logic;

    -- =============================================================================================
    -- Input interfaces to MFB merger
    -- =============================================================================================
    signal ptr_upd_rq_mfb_data    : std_logic_vector(PCIE_RQ_MFB_DATA'range);
    signal ptr_upd_rq_mfb_meta    : std_logic_vector(PCIE_RQ_MFB_META'range);
    signal ptr_upd_rq_mfb_sof     : std_logic_vector(PCIE_RQ_MFB_SOF'range);
    signal ptr_upd_rq_mfb_eof     : std_logic_vector(PCIE_RQ_MFB_EOF'range);
    signal ptr_upd_rq_mfb_sof_pos : std_logic_vector(PCIE_RQ_MFB_SOF_POS'range);
    signal ptr_upd_rq_mfb_eof_pos : std_logic_vector(PCIE_RQ_MFB_EOF_POS'range);
    signal ptr_upd_rq_mfb_src_rdy : std_logic;
    signal ptr_upd_rq_mfb_dst_rdy : std_logic;

    signal rx_dma_rq_mfb_data    : std_logic_vector(PCIE_RQ_MFB_DATA'range);
    signal rx_dma_rq_mfb_meta    : std_logic_vector(PCIE_RQ_MFB_META'range);
    signal rx_dma_rq_mfb_sof     : std_logic_vector(PCIE_RQ_MFB_SOF'range);
    signal rx_dma_rq_mfb_eof     : std_logic_vector(PCIE_RQ_MFB_EOF'range);
    signal rx_dma_rq_mfb_sof_pos : std_logic_vector(PCIE_RQ_MFB_SOF_POS'range);
    signal rx_dma_rq_mfb_eof_pos : std_logic_vector(PCIE_RQ_MFB_EOF_POS'range);
    signal rx_dma_rq_mfb_src_rdy : std_logic;
    signal rx_dma_rq_mfb_dst_rdy : std_logic;

    -- =============================================================================================
    -- MARK_DEBUG attributes for enabling ILA cores for the signals
    -- =============================================================================================
    -- attribute mark_debug : string;

    -- attribute mark_debug of USR_RX_MFB_META_CHAN     : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_META_HDR_META : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_DATA          : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SOF_POS       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_EOF_POS       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SOF           : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_EOF           : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SRC_RDY       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_DST_RDY       : signal is "true";

    -- attribute mark_debug of rx_stop_req_buff_ba : signal is "true";
    -- attribute mark_debug of rx_stop_req_p2p_en  : signal is "true";
    -- attribute mark_debug of rx_stop_req_hdp     : signal is "true";
    -- attribute mark_debug of rx_stop_req_hhp     : signal is "true";
    -- attribute mark_debug of rx_stop_req_en      : signal is "true";
    -- attribute mark_debug of rx_stop_req_ack     : signal is "true";

    -- attribute mark_debug of tx_stop_req_buff_ba : signal is "true";
    -- attribute mark_debug of tx_stop_req_p2p_en  : signal is "true";
    -- attribute mark_debug of tx_stop_req_hdp     : signal is "true";
    -- attribute mark_debug of tx_stop_req_hhp     : signal is "true";
    -- attribute mark_debug of tx_stop_req_en      : signal is "true";
    -- attribute mark_debug of tx_stop_req_ack     : signal is "true";

    -- attribute mark_debug of tx_rt_upd_ch      : signal is "true";
    -- attribute mark_debug of tx_rt_upd_buff_ba : signal is "true";
    -- attribute mark_debug of tx_rt_upd_p2p_en  : signal is "true";

    -- attribute mark_debug of tx_start_req_ch  : signal is "true";
    -- attribute mark_debug of tx_start_req_vld : signal is "true";
    -- attribute mark_debug of tx_start_req_ack : signal is "true";

    -- attribute mark_debug of tx_pkt_disp_upd_ch  : signal is "true";
    -- attribute mark_debug of tx_pkt_disp_upd_hdp : signal is "true";
    -- attribute mark_debug of tx_pkt_disp_upd_hhp : signal is "true";
    -- attribute mark_debug of tx_pkt_disp_upd_en  : signal is "true";

    -- attribute mark_debug of USR_TX_MFB_META_PKT_SIZE : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_META_CHAN     : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_META_HDR_META : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_DATA          : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_SOF_POS       : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_EOF_POS       : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_SOF           : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_EOF           : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_SRC_RDY       : signal is "true";
    -- attribute mark_debug of USR_TX_MFB_DST_RDY       : signal is "true";

    -- attribute mark_debug of ptr_upd_rq_mfb_data    : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_meta    : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_sof     : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_eof     : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_sof_pos : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_eof_pos : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_src_rdy : signal is "true";
    -- attribute mark_debug of ptr_upd_rq_mfb_dst_rdy : signal is "true";

    -- attribute mark_debug of rx_dma_rq_mfb_data    : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_meta    : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_sof     : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_eof     : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_sof_pos : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_eof_pos : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_src_rdy : signal is "true";
    -- attribute mark_debug of rx_dma_rq_mfb_dst_rdy : signal is "true";
begin

    rx_dma_calypte_g : if (RX_GEN_EN) generate
        rx_dma_calypte_i : entity work.RX_DMA_CALYPTE
        generic map (
            DEVICE   => DEVICE,
            MI_WIDTH => MI_WIDTH,

            USER_RX_MFB_REGIONS     => USR_MFB_REGIONS,
            USER_RX_MFB_REGION_SIZE => USR_MFB_REGION_SIZE,
            USER_RX_MFB_BLOCK_SIZE  => USR_MFB_BLOCK_SIZE,
            USER_RX_MFB_ITEM_WIDTH  => USR_MFB_ITEM_WIDTH,

            PCIE_UP_MFB_REGIONS     => PCIE_RQ_MFB_REGIONS,
            PCIE_UP_MFB_REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
            PCIE_UP_MFB_BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
            PCIE_UP_MFB_ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

            CHANNELS       => RX_CHANNELS,
            POINTER_WIDTH  => RX_PTR_WIDTH,
            SW_ADDR_WIDTH  => SW_ADDR_WIDTH,
            CNTRS_WIDTH    => DSP_CNT_WIDTH,
            HDR_META_WIDTH => HDR_META_WIDTH,
            PKT_SIZE_MAX   => USR_RX_PKT_SIZE_MAX,
            TRBUF_REG_EN   => TRBUF_REG_EN,
            PERF_CNTR_EN   => PERF_CNTR_EN
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

            PTR_UPD_BUFF_BA  => rx_stop_req_buff_ba,
            PTR_UPD_P2P_EN   => rx_stop_req_p2p_en,
            PTR_UPD_HDP      => rx_stop_req_hdp,
            PTR_UPD_HHP      => rx_stop_req_hhp,
            PTR_UPD_DISP_EN  => rx_stop_req_en,
            PTR_UPD_DISP_ACK => rx_stop_req_ack,

            USER_RX_MFB_META_HDR_META => USR_RX_MFB_META_HDR_META,
            USER_RX_MFB_META_CHAN     => USR_RX_MFB_META_CHAN,

            USER_RX_MFB_DATA    => USR_RX_MFB_DATA,
            USER_RX_MFB_SOF     => USR_RX_MFB_SOF,
            USER_RX_MFB_EOF     => USR_RX_MFB_EOF,
            USER_RX_MFB_SOF_POS => USR_RX_MFB_SOF_POS,
            USER_RX_MFB_EOF_POS => USR_RX_MFB_EOF_POS,
            USER_RX_MFB_SRC_RDY => USR_RX_MFB_SRC_RDY,
            USER_RX_MFB_DST_RDY => USR_RX_MFB_DST_RDY,

            PCIE_UP_MFB_DATA    => rx_dma_rq_mfb_data,
            PCIE_UP_MFB_META    => rx_dma_rq_mfb_meta,
            PCIE_UP_MFB_SOF     => rx_dma_rq_mfb_sof,
            PCIE_UP_MFB_EOF     => rx_dma_rq_mfb_eof,
            PCIE_UP_MFB_SOF_POS => rx_dma_rq_mfb_sof_pos,
            PCIE_UP_MFB_EOF_POS => rx_dma_rq_mfb_eof_pos,
            PCIE_UP_MFB_SRC_RDY => rx_dma_rq_mfb_src_rdy,
            PCIE_UP_MFB_DST_RDY => rx_dma_rq_mfb_dst_rdy
        );
    else generate
        mi_split_drd(0)  <= X"DEAD_BEAD";
        mi_split_ardy(0) <= mi_split_rd(0) or mi_split_wr(0);
        mi_split_drdy(0) <= mi_split_rd(0);

        rx_stop_req_buff_ba <= (others => '0');
        rx_stop_req_p2p_en  <= '0';
        rx_stop_req_hdp     <= (others => '0');
        rx_stop_req_hhp     <= (others => '0');
        rx_stop_req_en      <= '0';

        USR_RX_MFB_DST_RDY <= '1';

        PCIE_RQ_MFB_DATA    <= (others => '0');
        PCIE_RQ_MFB_SOF     <= (others => '0');
        PCIE_RQ_MFB_EOF     <= (others => '0');
        PCIE_RQ_MFB_SOF_POS <= (others => '0');
        PCIE_RQ_MFB_EOF_POS <= (others => '0');
        PCIE_RQ_MFB_SRC_RDY <= '0';
    end generate;

    tx_dma_calypte_g : if (TX_GEN_EN) generate
    begin
        tx_dma_calypte_i : entity work.TX_DMA_CALYPTE
        generic map (
            DEVICE   => DEVICE,
            MI_WIDTH => MI_WIDTH,

            USR_TX_MFB_REGIONS     => USR_MFB_REGIONS,
            USR_TX_MFB_REGION_SIZE => USR_MFB_REGION_SIZE,
            USR_TX_MFB_BLOCK_SIZE  => USR_MFB_BLOCK_SIZE,
            USR_TX_MFB_ITEM_WIDTH  => USR_MFB_ITEM_WIDTH,

            PCIE_CQ_MFB_REGIONS     => PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

            POINTER_WIDTH      => TX_PTR_WIDTH,
            CHANNELS           => TX_CHANNELS,
            CNTRS_WIDTH        => DSP_CNT_WIDTH,
            HDR_META_WIDTH     => HDR_META_WIDTH,
            ST_SP_DBG_SIGNAL_W => ST_SP_DBG_SIGNAL_W,
            PKT_SIZE_MAX       => USR_TX_PKT_SIZE_MAX
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            USR_TX_MFB_META_PKT_SIZE => USR_TX_MFB_META_PKT_SIZE,
            USR_TX_MFB_META_CHAN     => USR_TX_MFB_META_CHAN,
            USR_TX_MFB_META_HDR_META => USR_TX_MFB_META_HDR_META,

            USR_TX_MFB_DATA    => USR_TX_MFB_DATA,
            USR_TX_MFB_SOF     => USR_TX_MFB_SOF,
            USR_TX_MFB_EOF     => USR_TX_MFB_EOF,
            USR_TX_MFB_SOF_POS => USR_TX_MFB_SOF_POS,
            USR_TX_MFB_EOF_POS => USR_TX_MFB_EOF_POS,
            USR_TX_MFB_SRC_RDY => USR_TX_MFB_SRC_RDY,
            USR_TX_MFB_DST_RDY => USR_TX_MFB_DST_RDY,

            PCIE_CQ_MFB_DATA    => PCIE_CQ_MFB_DATA,
            PCIE_CQ_MFB_META    => PCIE_CQ_MFB_META,
            PCIE_CQ_MFB_SOF     => PCIE_CQ_MFB_SOF,
            PCIE_CQ_MFB_EOF     => PCIE_CQ_MFB_EOF,
            PCIE_CQ_MFB_SOF_POS => PCIE_CQ_MFB_SOF_POS,
            PCIE_CQ_MFB_EOF_POS => PCIE_CQ_MFB_EOF_POS,
            PCIE_CQ_MFB_SRC_RDY => PCIE_CQ_MFB_SRC_RDY,
            PCIE_CQ_MFB_DST_RDY => PCIE_CQ_MFB_DST_RDY,

            ST_SP_DBG_CHAN => ST_SP_DBG_CHAN,
            ST_SP_DBG_META => ST_SP_DBG_META,

            PKT_DISP_UPD_CH  => tx_pkt_disp_upd_ch,
            PKT_DISP_UPD_HDP => tx_pkt_disp_upd_hdp,
            PKT_DISP_UPD_HHP => tx_pkt_disp_upd_hhp,
            PKT_DISP_UPD_EN  => tx_pkt_disp_upd_en,

            RT_UPD_CH      => tx_rt_upd_ch,
            RT_UPD_BUFF_BA => tx_rt_upd_buff_ba,
            RT_UPD_P2P_EN  => tx_rt_upd_p2p_en,

            PTR_UPD_START_REQ_CH  => tx_start_req_ch,
            PTR_UPD_START_REQ_VLD => tx_start_req_vld,
            PTR_UPD_START_REQ_ACK => tx_start_req_ack,

            PTR_UPD_STOP_REQ_BUFF_BA => tx_stop_req_buff_ba,
            PTR_UPD_STOP_REQ_P2P_EN  => tx_stop_req_p2p_en,
            PTR_UPD_STOP_REQ_HDP     => tx_stop_req_hdp,
            PTR_UPD_STOP_REQ_HHP     => tx_stop_req_hhp,
            PTR_UPD_STOP_REQ_EN      => tx_stop_req_en,
            PTR_UPD_STOP_REQ_ACK     => tx_stop_req_ack,

            MI_ADDR => mi_split_addr(1),
            MI_DWR  => mi_split_dwr(1),
            MI_BE   => mi_split_be(1),
            MI_RD   => mi_split_rd(1),
            MI_WR   => mi_split_wr(1),
            MI_DRD  => mi_split_drd(1),
            MI_ARDY => mi_split_ardy(1),
            MI_DRDY => mi_split_drdy(1)
        );

    else generate
        mi_split_drd(1)  <= X"DEAD_BEAD";
        mi_split_ardy(1) <= mi_split_rd(1) or mi_split_wr(1);
        mi_split_drdy(1) <= mi_split_rd(1);

        USR_TX_MFB_META_PKT_SIZE <= (others => '0');
        USR_TX_MFB_META_CHAN     <= (others => '0');
        USR_TX_MFB_META_HDR_META <= (others => '0');

        USR_TX_MFB_DATA    <= (others => '0');
        USR_TX_MFB_SOF     <= (others => '0');
        USR_TX_MFB_EOF     <= (others => '0');
        USR_TX_MFB_SOF_POS <= (others => '0');
        USR_TX_MFB_EOF_POS <= (others => '0');
        USR_TX_MFB_SRC_RDY <= '0';

        PCIE_CQ_MFB_DST_RDY <= '1';

        ST_SP_DBG_CHAN <= (others => '0');
        ST_SP_DBG_META <= (others => '0');

        tx_pkt_disp_upd_ch  <= (others => '0');
        tx_pkt_disp_upd_hdp <= (others => '0');
        tx_pkt_disp_upd_hhp <= (others => '0');
        tx_pkt_disp_upd_en  <= '0';

        tx_rt_upd_buff_ba <= (others => '0');
        tx_rt_upd_p2p_en  <= '0';

        tx_start_req_ch  <= (others => '0');
        tx_start_req_vld <= '0';

        tx_stop_req_buff_ba <= (others => '0');
        tx_stop_req_p2p_en  <= '0';
        tx_stop_req_hdp     <= (others => '0');
        tx_stop_req_hhp     <= (others => '0');
        tx_stop_req_en      <= '0';
    end generate;

    dma_ptr_updater_i : entity work.DMA_PTR_UPDATER
    generic map (
        DEVICE            => DEVICE,

        MFB_REGIONS       => PCIE_RQ_MFB_REGIONS,
        MFB_REGION_SIZE   => PCIE_RQ_MFB_REGION_SIZE,
        MFB_BLOCK_SIZE    => PCIE_RQ_MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH    => PCIE_RQ_MFB_ITEM_WIDTH,

        RX_CHANNELS       => RX_CHANNELS,
        RX_PTR_WIDTH      => RX_PTR_WIDTH,

        TX_CHANNELS       => TX_CHANNELS,
        TX_DATA_PTR_WIDTH => TX_PTR_WIDTH,
        TX_HDR_PTR_WIDTH  => TX_PTR_WIDTH-3,
        TX_UPD_THRESHOLD  => USR_TX_PKT_SIZE_MAX/2
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_STOP_REQ_BUFF_BA => rx_stop_req_buff_ba,
        RX_STOP_REQ_P2P_EN  => rx_stop_req_p2p_en,
        RX_STOP_REQ_HDP     => rx_stop_req_hdp,
        RX_STOP_REQ_HHP     => rx_stop_req_hhp,
        RX_STOP_REQ_EN      => rx_stop_req_en,
        RX_STOP_REQ_ACK     => rx_stop_req_ack,

        TX_RT_UPD_CH        => tx_rt_upd_ch,
        TX_RT_UPD_BUFF_BA   => tx_rt_upd_buff_ba,
        TX_RT_UPD_P2P_EN    => tx_rt_upd_p2p_en,

        TX_PKT_DISP_CH      => tx_pkt_disp_upd_ch,
        TX_PKT_DISP_HDP     => tx_pkt_disp_upd_hdp,
        TX_PKT_DISP_HHP     => tx_pkt_disp_upd_hhp,
        TX_PKT_DISP_EN      => tx_pkt_disp_upd_en,

        TX_START_REQ_CH     => tx_start_req_ch,
        TX_START_REQ_VLD    => tx_start_req_vld,
        TX_START_REQ_ACK    => tx_start_req_ack,

        TX_STOP_REQ_BUFF_BA => tx_stop_req_buff_ba,
        TX_STOP_REQ_P2P_EN  => tx_stop_req_p2p_en,
        TX_STOP_REQ_HDP     => tx_stop_req_hdp,
        TX_STOP_REQ_HHP     => tx_stop_req_hhp,
        TX_STOP_REQ_EN      => tx_stop_req_en,
        TX_STOP_REQ_ACK     => tx_stop_req_ack,

        PCIE_RQ_MFB_DATA    => ptr_upd_rq_mfb_data,
        PCIE_RQ_MFB_META    => ptr_upd_rq_mfb_meta,
        PCIE_RQ_MFB_SOF     => ptr_upd_rq_mfb_sof,
        PCIE_RQ_MFB_EOF     => ptr_upd_rq_mfb_eof,
        PCIE_RQ_MFB_SOF_POS => ptr_upd_rq_mfb_sof_pos,
        PCIE_RQ_MFB_EOF_POS => ptr_upd_rq_mfb_eof_pos,
        PCIE_RQ_MFB_SRC_RDY => ptr_upd_rq_mfb_src_rdy,
        PCIE_RQ_MFB_DST_RDY => ptr_upd_rq_mfb_dst_rdy
    );

    pcie_rq_mfb_merger_i : entity work.MFB_MERGER_SIMPLE
    generic map (
        REGIONS     => PCIE_RQ_MFB_REGIONS,
        REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
        BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
        ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

        META_WIDTH  => PCIE_RQ_META_WIDTH,
        MASKING_EN  => false,
        CNT_MAX     => 2**3
    )
    port map (
        CLK             => CLK,
        RST             => RESET,

        RX_MFB0_DATA    => rx_dma_rq_mfb_data,
        RX_MFB0_META    => rx_dma_rq_mfb_meta,
        RX_MFB0_SOF     => rx_dma_rq_mfb_sof,
        RX_MFB0_SOF_POS => rx_dma_rq_mfb_sof_pos,
        RX_MFB0_EOF     => rx_dma_rq_mfb_eof,
        RX_MFB0_EOF_POS => rx_dma_rq_mfb_eof_pos,
        RX_MFB0_SRC_RDY => rx_dma_rq_mfb_src_rdy,
        RX_MFB0_DST_RDY => rx_dma_rq_mfb_dst_rdy,

        RX_MFB1_DATA    => ptr_upd_rq_mfb_data,
        RX_MFB1_META    => ptr_upd_rq_mfb_meta,
        RX_MFB1_SOF     => ptr_upd_rq_mfb_sof,
        RX_MFB1_SOF_POS => ptr_upd_rq_mfb_sof_pos,
        RX_MFB1_EOF     => ptr_upd_rq_mfb_eof,
        RX_MFB1_EOF_POS => ptr_upd_rq_mfb_eof_pos,
        RX_MFB1_SRC_RDY => ptr_upd_rq_mfb_src_rdy,
        RX_MFB1_DST_RDY => ptr_upd_rq_mfb_dst_rdy,

        TX_MFB_DATA     => PCIE_RQ_MFB_DATA,
        TX_MFB_META     => PCIE_RQ_MFB_META,
        TX_MFB_SOF      => PCIE_RQ_MFB_SOF,
        TX_MFB_SOF_POS  => PCIE_RQ_MFB_SOF_POS,
        TX_MFB_EOF      => PCIE_RQ_MFB_EOF,
        TX_MFB_EOF_POS  => PCIE_RQ_MFB_EOF_POS,
        TX_MFB_SRC_RDY  => PCIE_RQ_MFB_SRC_RDY,
        TX_MFB_DST_RDY  => PCIE_RQ_MFB_DST_RDY
    );

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH => MI_WIDTH,
        DATA_WIDTH => MI_WIDTH,
        META_WIDTH => 0,
        PORTS      => 2,
        PIPE_OUT   => (others => FALSE),

        ADDR_BASES => 2,
        ADDR_BASE  => MI_SPLIT_BASES,
        ADDR_MASK  => x"00200000",

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
end architecture;
