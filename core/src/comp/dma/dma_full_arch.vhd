-- dma.vhd: DMA Module Wrapper
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.dma_bus_pack.all;

architecture FULL of DMA is

    constant IUSR_MVB_ITEMS    : natural                         := tsel(DMA_400G_DEMO, 4, USR_MVB_ITEMS);
    constant IUSR_MFB_REGIONS  : natural                         := tsel(DMA_400G_DEMO, 4, USR_MFB_REGIONS);
    constant GLS_MI_OFFSET     : std_logic_vector(32-1 downto 0) := X"0000_0200";

    function gls_mi_addr_base_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(DMA_STREAMS-1 downto 0)(32-1 downto 0);
    begin
        for i in 0 to DMA_STREAMS-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(GLS_MI_OFFSET), 32));
        end loop;
        return mi_addr_base_var;
    end function;

    -- =====================================================================
    --  MI Splitting for multiple GLS
    -- =====================================================================

    signal gls_mi_addr : slv_array_t (DMA_STREAMS -1 downto 0)(32 -1 downto 0);
    signal gls_mi_dwr  : slv_array_t (DMA_STREAMS -1 downto 0)(32 -1 downto 0);
    signal gls_mi_be   : slv_array_t (DMA_STREAMS -1 downto 0)(32/8 -1 downto 0);
    signal gls_mi_rd   : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal gls_mi_wr   : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal gls_mi_drd  : slv_array_t (DMA_STREAMS -1 downto 0)(32 -1 downto 0);
    signal gls_mi_ardy : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal gls_mi_drdy : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =====================================================================

    signal rx_usr_mvb_len_int      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1)-1 downto 0);
    signal rx_usr_mvb_hdr_meta_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
    signal rx_usr_mvb_channel_int  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(RX_CHANNELS) -1 downto 0);
    signal rx_usr_mvb_discard_int  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*1 -1 downto 0);
    signal rx_usr_mvb_vld_int      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS -1 downto 0);
    signal rx_usr_mvb_src_rdy_int  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal rx_usr_mvb_dst_rdy_int  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal rx_usr_mfb_data_int    : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal rx_usr_mfb_sof_int     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal rx_usr_mfb_eof_int     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal rx_usr_mfb_sof_pos_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
    signal rx_usr_mfb_eof_pos_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
    signal rx_usr_mfb_src_rdy_int : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal rx_usr_mfb_dst_rdy_int : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal tx_usr_mvb_len_int      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(USR_TX_PKT_SIZE_MAX+1)-1 downto 0);
    signal tx_usr_mvb_hdr_meta_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
    signal tx_usr_mvb_channel_int  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(TX_CHANNELS) -1 downto 0);
    signal tx_usr_mvb_vld_int      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS -1 downto 0);
    signal tx_usr_mvb_src_rdy_int  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal tx_usr_mvb_dst_rdy_int  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal tx_usr_mfb_data_int    : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal tx_usr_mfb_sof_int     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal tx_usr_mfb_eof_int     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal tx_usr_mfb_sof_pos_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
    signal tx_usr_mfb_eof_pos_int : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
    signal tx_usr_mfb_src_rdy_int : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal tx_usr_mfb_dst_rdy_int : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =====================================================================
    --  GEN_LOOP_SWITCH -> DMA Module interface
    -- =====================================================================

    signal dma_rx_usr_mvb_len      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1)-1 downto 0);
    signal dma_rx_usr_mvb_hdr_meta : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
    signal dma_rx_usr_mvb_channel  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(RX_CHANNELS) -1 downto 0);
    signal dma_rx_usr_mvb_discard  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*1 -1 downto 0);
    signal dma_rx_usr_mvb_vld      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS -1 downto 0);
    signal dma_rx_usr_mvb_src_rdy  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal dma_rx_usr_mvb_dst_rdy  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal dma_rx_usr_mfb_data    : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rx_usr_mfb_sof     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal dma_rx_usr_mfb_eof     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal dma_rx_usr_mfb_sof_pos : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
    signal dma_rx_usr_mfb_eof_pos : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
    signal dma_rx_usr_mfb_src_rdy : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal dma_rx_usr_mfb_dst_rdy : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  DMA Module -> GEN_LOOP_SWITCH interface
    -- =====================================================================

    signal dma_tx_usr_mvb_len      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(USR_TX_PKT_SIZE_MAX+1)-1 downto 0);
    signal dma_tx_usr_mvb_hdr_meta : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH -1 downto 0);
    signal dma_tx_usr_mvb_channel  : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS*log2(TX_CHANNELS) -1 downto 0);
    signal dma_tx_usr_mvb_vld      : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MVB_ITEMS -1 downto 0);
    signal dma_tx_usr_mvb_src_rdy  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal dma_tx_usr_mvb_dst_rdy  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal dma_tx_usr_mfb_data    : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_tx_usr_mfb_sof     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal dma_tx_usr_mfb_eof     : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS -1 downto 0);
    signal dma_tx_usr_mfb_sof_pos : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
    signal dma_tx_usr_mfb_eof_pos : slv_array_t(DMA_STREAMS -1 downto 0)(IUSR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
    signal dma_tx_usr_mfb_src_rdy : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal dma_tx_usr_mfb_dst_rdy : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =====================================================================

begin

    -- =====================================================================
    --  DMA Module
    -- =====================================================================

    dma_i : entity work.DMA_WRAPPER
        generic map(
            DEVICE  => DEVICE,

            DMA_STREAMS     => DMA_STREAMS,
            DMA_ENDPOINTS   => DMA_ENDPOINTS,
            PCIE_ENDPOINTS  => PCIE_ENDPOINTS,

            USR_MVB_ITEMS       => IUSR_MVB_ITEMS,
            USR_MFB_REGIONS     => IUSR_MFB_REGIONS,
            USR_MFB_REGION_SIZE => USR_MFB_REGION_SIZE,
            USR_MFB_BLOCK_SIZE  => USR_MFB_BLOCK_SIZE,
            USR_MFB_ITEM_WIDTH  => USR_MFB_ITEM_WIDTH,

            USR_RX_PKT_SIZE_MAX => USR_RX_PKT_SIZE_MAX,
            USR_TX_PKT_SIZE_MAX => USR_TX_PKT_SIZE_MAX,

            PCIE_MPS      => PCIE_MPS,
            PCIE_MRRS     => PCIE_MRRS,
            DMA_TAG_WIDTH => DMA_TAG_WIDTH,

            PCIE_RQ_MFB_REGIONS     => PCIE_RQ_MFB_REGIONS,
            PCIE_RQ_MFB_REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
            PCIE_RQ_MFB_BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
            PCIE_RQ_MFB_ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

            PCIE_RC_MFB_REGIONS     => PCIE_RC_MFB_REGIONS,
            PCIE_RC_MFB_REGION_SIZE => PCIE_RC_MFB_REGION_SIZE,
            PCIE_RC_MFB_BLOCK_SIZE  => PCIE_RC_MFB_BLOCK_SIZE,
            PCIE_RC_MFB_ITEM_WIDTH  => PCIE_RC_MFB_ITEM_WIDTH,

            PCIE_CQ_MFB_REGIONS     => PCIE_CQ_MFB_REGIONS,
            PCIE_CQ_MFB_REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
            PCIE_CQ_MFB_BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
            PCIE_CQ_MFB_ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

            PCIE_CC_MFB_REGIONS     => PCIE_CC_MFB_REGIONS,
            PCIE_CC_MFB_REGION_SIZE => PCIE_CC_MFB_REGION_SIZE,
            PCIE_CC_MFB_BLOCK_SIZE  => PCIE_CC_MFB_BLOCK_SIZE,
            PCIE_CC_MFB_ITEM_WIDTH  => PCIE_CC_MFB_ITEM_WIDTH,

            HDR_META_WIDTH => HDR_META_WIDTH,

            RX_CHANNELS      => RX_CHANNELS,
            RX_DP_WIDTH      => RX_DP_WIDTH,
            RX_HP_WIDTH      => RX_HP_WIDTH,
            RX_BLOCKING_MODE => RX_BLOCKING_MODE,

            TX_CHANNELS     => TX_CHANNELS,
            TX_SEL_CHANNELS => TX_SEL_CHANNELS,
            TX_DP_WIDTH     => TX_DP_WIDTH,

            DSP_CNT_WIDTH => 48,

            RX_GEN_EN => RX_GEN_EN,
            TX_GEN_EN => TX_GEN_EN,

            SPEED_METER_EN  => TRUE,
            DBG_CNTR_EN     => DBG_CNTR_EN,
            USR_EQ_DMA      => USR_EQ_DMA,
            CROX_EQ_DMA     => CROX_EQ_DMA,
            CROX_DOUBLE_DMA => CROX_DOUBLE_DMA,

            MI_WIDTH => 32
            )
        port map(
            DMA_CLK   => DMA_CLK,
            DMA_RESET => DMA_RESET,

            CROX_CLK   => CROX_CLK,
            CROX_RESET => CROX_RESET,

            USR_CLK   => USR_CLK,
            USR_RESET => USR_RESET,

            MI_CLK   => MI_CLK,
            MI_RESET => MI_RESET,

            PCIE_USR_CLK   => PCIE_USR_CLK,
            PCIE_USR_RESET => PCIE_USR_RESET,

            RX_USR_MVB_LEN      => dma_rx_usr_mvb_len,
            RX_USR_MVB_HDR_META => dma_rx_usr_mvb_hdr_meta,
            RX_USR_MVB_CHANNEL  => dma_rx_usr_mvb_channel,
            RX_USR_MVB_DISCARD  => dma_rx_usr_mvb_discard,
            RX_USR_MVB_VLD      => dma_rx_usr_mvb_vld,
            RX_USR_MVB_SRC_RDY  => dma_rx_usr_mvb_src_rdy,
            RX_USR_MVB_DST_RDY  => dma_rx_usr_mvb_dst_rdy,

            RX_USR_MFB_DATA    => dma_rx_usr_mfb_data,
            RX_USR_MFB_SOF     => dma_rx_usr_mfb_sof,
            RX_USR_MFB_EOF     => dma_rx_usr_mfb_eof,
            RX_USR_MFB_SOF_POS => dma_rx_usr_mfb_sof_pos,
            RX_USR_MFB_EOF_POS => dma_rx_usr_mfb_eof_pos,
            RX_USR_MFB_SRC_RDY => dma_rx_usr_mfb_src_rdy,
            RX_USR_MFB_DST_RDY => dma_rx_usr_mfb_dst_rdy,

            TX_USR_MVB_LEN      => dma_tx_usr_mvb_len,
            TX_USR_MVB_HDR_META => dma_tx_usr_mvb_hdr_meta,
            TX_USR_MVB_CHANNEL  => dma_tx_usr_mvb_channel,
            TX_USR_MVB_VLD      => dma_tx_usr_mvb_vld,
            TX_USR_MVB_SRC_RDY  => dma_tx_usr_mvb_src_rdy,
            TX_USR_MVB_DST_RDY  => dma_tx_usr_mvb_dst_rdy,

            TX_USR_MFB_DATA    => dma_tx_usr_mfb_data,
            TX_USR_MFB_SOF     => dma_tx_usr_mfb_sof,
            TX_USR_MFB_EOF     => dma_tx_usr_mfb_eof,
            TX_USR_MFB_SOF_POS => dma_tx_usr_mfb_sof_pos,
            TX_USR_MFB_EOF_POS => dma_tx_usr_mfb_eof_pos,
            TX_USR_MFB_SRC_RDY => dma_tx_usr_mfb_src_rdy,
            TX_USR_MFB_DST_RDY => dma_tx_usr_mfb_dst_rdy,

            TX_USR_CHOKE_CHANS => TX_USR_CHOKE_CHANS,

            PCIE_RQ_MVB_DATA    => PCIE_RQ_MVB_DATA,
            PCIE_RQ_MVB_VLD     => PCIE_RQ_MVB_VLD,
            PCIE_RQ_MVB_SRC_RDY => PCIE_RQ_MVB_SRC_RDY,
            PCIE_RQ_MVB_DST_RDY => PCIE_RQ_MVB_DST_RDY,

            PCIE_RQ_MFB_DATA    => PCIE_RQ_MFB_DATA,
            PCIE_RQ_MFB_META    => PCIE_RQ_MFB_META,
            PCIE_RQ_MFB_SOF     => PCIE_RQ_MFB_SOF,
            PCIE_RQ_MFB_EOF     => PCIE_RQ_MFB_EOF,
            PCIE_RQ_MFB_SOF_POS => PCIE_RQ_MFB_SOF_POS,
            PCIE_RQ_MFB_EOF_POS => PCIE_RQ_MFB_EOF_POS,
            PCIE_RQ_MFB_SRC_RDY => PCIE_RQ_MFB_SRC_RDY,
            PCIE_RQ_MFB_DST_RDY => PCIE_RQ_MFB_DST_RDY,

            PCIE_RC_MVB_DATA    => PCIE_RC_MVB_DATA,
            PCIE_RC_MVB_VLD     => PCIE_RC_MVB_VLD,
            PCIE_RC_MVB_SRC_RDY => PCIE_RC_MVB_SRC_RDY,
            PCIE_RC_MVB_DST_RDY => PCIE_RC_MVB_DST_RDY,

            PCIE_RC_MFB_DATA    => PCIE_RC_MFB_DATA,
            PCIE_RC_MFB_SOF     => PCIE_RC_MFB_SOF,
            PCIE_RC_MFB_EOF     => PCIE_RC_MFB_EOF,
            PCIE_RC_MFB_SOF_POS => PCIE_RC_MFB_SOF_POS,
            PCIE_RC_MFB_EOF_POS => PCIE_RC_MFB_EOF_POS,
            PCIE_RC_MFB_SRC_RDY => PCIE_RC_MFB_SRC_RDY,
            PCIE_RC_MFB_DST_RDY => PCIE_RC_MFB_DST_RDY,

            PCIE_CQ_MFB_DATA    => PCIE_CQ_MFB_DATA,
            PCIE_CQ_MFB_META    => PCIE_CQ_MFB_META,
            PCIE_CQ_MFB_SOF     => PCIE_CQ_MFB_SOF,
            PCIE_CQ_MFB_EOF     => PCIE_CQ_MFB_EOF,
            PCIE_CQ_MFB_SOF_POS => PCIE_CQ_MFB_SOF_POS,
            PCIE_CQ_MFB_EOF_POS => PCIE_CQ_MFB_EOF_POS,
            PCIE_CQ_MFB_SRC_RDY => PCIE_CQ_MFB_SRC_RDY,
            PCIE_CQ_MFB_DST_RDY => PCIE_CQ_MFB_DST_RDY,

            PCIE_CC_MFB_DATA    => PCIE_CC_MFB_DATA,
            PCIE_CC_MFB_META    => PCIE_CC_MFB_META,
            PCIE_CC_MFB_SOF     => PCIE_CC_MFB_SOF,
            PCIE_CC_MFB_EOF     => PCIE_CC_MFB_EOF,
            PCIE_CC_MFB_SOF_POS => PCIE_CC_MFB_SOF_POS,
            PCIE_CC_MFB_EOF_POS => PCIE_CC_MFB_EOF_POS,
            PCIE_CC_MFB_SRC_RDY => PCIE_CC_MFB_SRC_RDY,
            PCIE_CC_MFB_DST_RDY => PCIE_CC_MFB_DST_RDY,

            MI_ADDR => MI_ADDR,
            MI_DWR  => MI_DWR,
            MI_BE   => MI_BE,
            MI_RD   => MI_RD,
            MI_WR   => MI_WR,
            MI_DRD  => MI_DRD,
            MI_ARDY => MI_ARDY,
            MI_DRDY => MI_DRDY
            );

    -- =====================================================================

    dma_demo_off_g : if (not DMA_400G_DEMO) generate

        rx_usr_mvb_len_int      <= RX_USR_MVB_LEN;
        rx_usr_mvb_hdr_meta_int <= RX_USR_MVB_HDR_META;
        rx_usr_mvb_channel_int  <= RX_USR_MVB_CHANNEL;
        rx_usr_mvb_discard_int  <= RX_USR_MVB_DISCARD;
        rx_usr_mvb_vld_int      <= RX_USR_MVB_VLD;
        rx_usr_mvb_src_rdy_int  <= RX_USR_MVB_SRC_RDY;
        RX_USR_MVB_DST_RDY      <= rx_usr_mvb_dst_rdy_int;

        rx_usr_mfb_data_int    <= RX_USR_MFB_DATA;
        rx_usr_mfb_sof_int     <= RX_USR_MFB_SOF;
        rx_usr_mfb_eof_int     <= RX_USR_MFB_EOF;
        rx_usr_mfb_sof_pos_int <= RX_USR_MFB_SOF_POS;
        rx_usr_mfb_eof_pos_int <= RX_USR_MFB_EOF_POS;
        rx_usr_mfb_src_rdy_int <= RX_USR_MFB_SRC_RDY;
        RX_USR_MFB_DST_RDY     <= rx_usr_mfb_dst_rdy_int;

        TX_USR_MVB_LEN         <= tx_usr_mvb_len_int;
        TX_USR_MVB_HDR_META    <= tx_usr_mvb_hdr_meta_int;
        TX_USR_MVB_CHANNEL     <= tx_usr_mvb_channel_int;
        TX_USR_MVB_VLD         <= tx_usr_mvb_vld_int;
        TX_USR_MVB_SRC_RDY     <= tx_usr_mvb_src_rdy_int;
        tx_usr_mvb_dst_rdy_int <= TX_USR_MVB_DST_RDY;

        TX_USR_MFB_DATA        <= tx_usr_mfb_data_int;
        TX_USR_MFB_SOF         <= tx_usr_mfb_sof_int;
        TX_USR_MFB_EOF         <= tx_usr_mfb_eof_int;
        TX_USR_MFB_SOF_POS     <= tx_usr_mfb_sof_pos_int;
        TX_USR_MFB_EOF_POS     <= tx_usr_mfb_eof_pos_int;
        TX_USR_MFB_SRC_RDY     <= tx_usr_mfb_src_rdy_int;
        tx_usr_mfb_dst_rdy_int <= TX_USR_MFB_DST_RDY;

    end generate;

    dma_demo_on_g : if (DMA_400G_DEMO) generate
        rx_usr_mvb_len_int      <= (others => (others => '0'));
        rx_usr_mvb_hdr_meta_int <= (others => (others => '0'));
        rx_usr_mvb_channel_int  <= (others => (others => '0'));
        rx_usr_mvb_discard_int  <= (others => (others => '0'));
        rx_usr_mvb_vld_int      <= (others => (others => '0'));
        rx_usr_mvb_src_rdy_int  <= (others => '0');
        RX_USR_MVB_DST_RDY      <= (others => '1');

        rx_usr_mfb_data_int    <= (others => (others => '0'));
        rx_usr_mfb_sof_int     <= (others => (others => '0'));
        rx_usr_mfb_eof_int     <= (others => (others => '0'));
        rx_usr_mfb_sof_pos_int <= (others => (others => '0'));
        rx_usr_mfb_eof_pos_int <= (others => (others => '0'));
        rx_usr_mfb_src_rdy_int <= (others => '0');
        RX_USR_MFB_DST_RDY     <= (others => '1');

        TX_USR_MVB_LEN         <= (others => (others => '0'));
        TX_USR_MVB_HDR_META    <= (others => (others => '0'));
        TX_USR_MVB_CHANNEL     <= (others => (others => '0'));
        TX_USR_MVB_VLD         <= (others => (others => '0'));
        TX_USR_MVB_SRC_RDY     <= (others => '0');
        tx_usr_mvb_dst_rdy_int <= (others => '1');

        TX_USR_MFB_DATA        <= (others => (others => '0'));
        TX_USR_MFB_SOF         <= (others => (others => '0'));
        TX_USR_MFB_EOF         <= (others => (others => '0'));
        TX_USR_MFB_SOF_POS     <= (others => (others => '0'));
        TX_USR_MFB_EOF_POS     <= (others => (others => '0'));
        TX_USR_MFB_SRC_RDY     <= (others => '0');
        tx_usr_mfb_dst_rdy_int <= (others => '1');
    end generate;

    gls_mi_split_g: if (GEN_LOOP_EN or DMA_400G_DEMO) generate
        mi_splitter_gls_i : entity work.MI_SPLITTER_PLUS_GEN
            generic map(
                ADDR_WIDTH => 32,
                DATA_WIDTH => 32,
                META_WIDTH => 0,
                PORTS      => DMA_STREAMS,
                ADDR_BASE  => gls_mi_addr_base_f,
                DEVICE     => DEVICE
                )
            port map(
                CLK   => MI_CLK,
                RESET => MI_RESET,

                RX_DWR  => GEN_LOOP_MI_DWR,
                RX_ADDR => GEN_LOOP_MI_ADDR,
                RX_BE   => GEN_LOOP_MI_BE,
                RX_RD   => GEN_LOOP_MI_RD,
                RX_WR   => GEN_LOOP_MI_WR,
                RX_ARDY => GEN_LOOP_MI_ARDY,
                RX_DRD  => GEN_LOOP_MI_DRD,
                RX_DRDY => GEN_LOOP_MI_DRDY,

                TX_DWR  => gls_mi_dwr,
                TX_ADDR => gls_mi_addr,
                TX_BE   => gls_mi_be,
                TX_RD   => gls_mi_rd,
                TX_WR   => gls_mi_wr,
                TX_ARDY => gls_mi_ardy,
                TX_DRD  => gls_mi_drd,
                TX_DRDY => gls_mi_drdy
                );
    else generate
        GEN_LOOP_MI_ARDY <= GEN_LOOP_MI_RD or GEN_LOOP_MI_WR;
        GEN_LOOP_MI_DRD  <= x"0000DEAD";
        GEN_LOOP_MI_DRDY <= GEN_LOOP_MI_RD;
    end generate;

    gls_g : for i in 0 to DMA_STREAMS-1 generate
        gls_en_g : if (GEN_LOOP_EN or DMA_400G_DEMO) generate
            gen_loop_switch_i : entity work.GEN_LOOP_SWITCH
                generic map(
                    REGIONS         => IUSR_MFB_REGIONS,
                    REGION_SIZE     => USR_MFB_REGION_SIZE,
                    BLOCK_SIZE      => USR_MFB_BLOCK_SIZE,
                    ITEM_WIDTH      => USR_MFB_ITEM_WIDTH,
                    PKT_MTU         => USR_RX_PKT_SIZE_MAX,
                    RX_DMA_CHANNELS => RX_CHANNELS,
                    TX_DMA_CHANNELS => TX_CHANNELS,
                    HDR_META_WIDTH  => HDR_META_WIDTH,
                    RX_HDR_INS_EN   => FALSE,  -- only enable for version 1 to DMA Medusa
                    SAME_CLK        => FALSE,
                    MI_PIPE_EN      => TRUE,
                    DEVICE          => DEVICE
                    )
                port map(
                    MI_CLK   => MI_CLK,
                    MI_RESET => MI_RESET,
                    MI_DWR   => gls_mi_dwr(i),
                    MI_ADDR  => gls_mi_addr(i),
                    MI_BE    => gls_mi_be(i),
                    MI_RD    => gls_mi_rd(i),
                    MI_WR    => gls_mi_wr(i),
                    MI_ARDY  => gls_mi_ardy(i),
                    MI_DRD   => gls_mi_drd(i),
                    MI_DRDY  => gls_mi_drdy(i),

                    CLK   => USR_CLK,
                    RESET => USR_RESET,

                    ETH_RX_MVB_LEN      => rx_usr_mvb_len_int(i),
                    ETH_RX_MVB_HDR_META => rx_usr_mvb_hdr_meta_int(i),
                    ETH_RX_MVB_CHANNEL  => rx_usr_mvb_channel_int(i),
                    ETH_RX_MVB_DISCARD  => rx_usr_mvb_discard_int(i),
                    ETH_RX_MVB_VLD      => rx_usr_mvb_vld_int(i),
                    ETH_RX_MVB_SRC_RDY  => rx_usr_mvb_src_rdy_int(i),
                    ETH_RX_MVB_DST_RDY  => rx_usr_mvb_dst_rdy_int(i),

                    ETH_RX_MFB_DATA    => rx_usr_mfb_data_int(i),
                    ETH_RX_MFB_SOF     => rx_usr_mfb_sof_int(i),
                    ETH_RX_MFB_EOF     => rx_usr_mfb_eof_int(i),
                    ETH_RX_MFB_SOF_POS => rx_usr_mfb_sof_pos_int(i),
                    ETH_RX_MFB_EOF_POS => rx_usr_mfb_eof_pos_int(i),
                    ETH_RX_MFB_SRC_RDY => rx_usr_mfb_src_rdy_int(i),
                    ETH_RX_MFB_DST_RDY => rx_usr_mfb_dst_rdy_int(i),

                    ETH_TX_MVB_LEN      => tx_usr_mvb_len_int(i),
                    ETH_TX_MVB_HDR_META => tx_usr_mvb_hdr_meta_int(i),
                    ETH_TX_MVB_CHANNEL  => tx_usr_mvb_channel_int(i),
                    ETH_TX_MVB_VLD      => tx_usr_mvb_vld_int(i),
                    ETH_TX_MVB_SRC_RDY  => tx_usr_mvb_src_rdy_int(i),
                    ETH_TX_MVB_DST_RDY  => tx_usr_mvb_dst_rdy_int(i),

                    ETH_TX_MFB_DATA    => tx_usr_mfb_data_int(i),
                    ETH_TX_MFB_SOF     => tx_usr_mfb_sof_int(i),
                    ETH_TX_MFB_EOF     => tx_usr_mfb_eof_int(i),
                    ETH_TX_MFB_SOF_POS => tx_usr_mfb_sof_pos_int(i),
                    ETH_TX_MFB_EOF_POS => tx_usr_mfb_eof_pos_int(i),
                    ETH_TX_MFB_SRC_RDY => tx_usr_mfb_src_rdy_int(i),
                    ETH_TX_MFB_DST_RDY => tx_usr_mfb_dst_rdy_int(i),

                    DMA_RX_MVB_LEN      => dma_rx_usr_mvb_len(i),
                    DMA_RX_MVB_HDR_META => dma_rx_usr_mvb_hdr_meta(i),
                    DMA_RX_MVB_CHANNEL  => dma_rx_usr_mvb_channel(i),
                    DMA_RX_MVB_DISCARD  => dma_rx_usr_mvb_discard(i),
                    DMA_RX_MVB_VLD      => dma_rx_usr_mvb_vld(i),
                    DMA_RX_MVB_SRC_RDY  => dma_rx_usr_mvb_src_rdy(i),
                    DMA_RX_MVB_DST_RDY  => dma_rx_usr_mvb_dst_rdy(i),

                    DMA_RX_MFB_DATA    => dma_rx_usr_mfb_data(i),
                    DMA_RX_MFB_SOF     => dma_rx_usr_mfb_sof(i),
                    DMA_RX_MFB_EOF     => dma_rx_usr_mfb_eof(i),
                    DMA_RX_MFB_SOF_POS => dma_rx_usr_mfb_sof_pos(i),
                    DMA_RX_MFB_EOF_POS => dma_rx_usr_mfb_eof_pos(i),
                    DMA_RX_MFB_SRC_RDY => dma_rx_usr_mfb_src_rdy(i),
                    DMA_RX_MFB_DST_RDY => dma_rx_usr_mfb_dst_rdy(i),

                    DMA_TX_MVB_LEN      => dma_tx_usr_mvb_len(i),
                    DMA_TX_MVB_HDR_META => dma_tx_usr_mvb_hdr_meta(i),
                    DMA_TX_MVB_CHANNEL  => dma_tx_usr_mvb_channel(i),
                    DMA_TX_MVB_VLD      => dma_tx_usr_mvb_vld(i),
                    DMA_TX_MVB_SRC_RDY  => dma_tx_usr_mvb_src_rdy(i),
                    DMA_TX_MVB_DST_RDY  => dma_tx_usr_mvb_dst_rdy(i),

                    DMA_TX_MFB_DATA    => dma_tx_usr_mfb_data(i),
                    DMA_TX_MFB_SOF     => dma_tx_usr_mfb_sof(i),
                    DMA_TX_MFB_EOF     => dma_tx_usr_mfb_eof(i),
                    DMA_TX_MFB_SOF_POS => dma_tx_usr_mfb_sof_pos(i),
                    DMA_TX_MFB_EOF_POS => dma_tx_usr_mfb_eof_pos(i),
                    DMA_TX_MFB_SRC_RDY => dma_tx_usr_mfb_src_rdy(i),
                    DMA_TX_MFB_DST_RDY => dma_tx_usr_mfb_dst_rdy(i)
                    );
        else generate

            dma_rx_usr_mvb_len(i)       <= rx_usr_mvb_len_int(i);
            dma_rx_usr_mvb_hdr_meta(i)  <= rx_usr_mvb_hdr_meta_int(i);
            dma_rx_usr_mvb_channel(i)   <= rx_usr_mvb_channel_int(i);
            dma_rx_usr_mvb_discard(i)   <= rx_usr_mvb_discard_int(i);
            dma_rx_usr_mvb_vld(i)       <= rx_usr_mvb_vld_int(i);
            dma_rx_usr_mvb_src_rdy(i)   <= rx_usr_mvb_src_rdy_int(i);
            rx_usr_mvb_dst_rdy_int(i)   <= dma_rx_usr_mvb_dst_rdy(i);

            dma_rx_usr_mfb_data(i)      <= rx_usr_mfb_data_int(i);
            dma_rx_usr_mfb_sof(i)       <= rx_usr_mfb_sof_int(i);
            dma_rx_usr_mfb_eof(i)       <= rx_usr_mfb_eof_int(i);
            dma_rx_usr_mfb_sof_pos(i)   <= rx_usr_mfb_sof_pos_int(i);
            dma_rx_usr_mfb_eof_pos(i)   <= rx_usr_mfb_eof_pos_int(i);
            dma_rx_usr_mfb_src_rdy(i)   <= rx_usr_mfb_src_rdy_int(i);
            rx_usr_mfb_dst_rdy_int(i)   <= dma_rx_usr_mfb_dst_rdy(i);

            tx_usr_mvb_len_int(i)       <= dma_tx_usr_mvb_len(i);
            tx_usr_mvb_hdr_meta_int(i)  <= dma_tx_usr_mvb_hdr_meta(i);
            tx_usr_mvb_channel_int(i)   <= dma_tx_usr_mvb_channel(i);
            tx_usr_mvb_vld_int(i)       <= dma_tx_usr_mvb_vld(i);
            tx_usr_mvb_src_rdy_int(i)   <= dma_tx_usr_mvb_src_rdy(i);
            dma_tx_usr_mvb_dst_rdy(i)   <= tx_usr_mvb_dst_rdy_int(i);

            tx_usr_mfb_data_int(i)      <= dma_tx_usr_mfb_data(i);
            tx_usr_mfb_sof_int(i)       <= dma_tx_usr_mfb_sof(i);
            tx_usr_mfb_eof_int(i)       <= dma_tx_usr_mfb_eof(i);
            tx_usr_mfb_sof_pos_int(i)   <= dma_tx_usr_mfb_sof_pos(i);
            tx_usr_mfb_eof_pos_int(i)   <= dma_tx_usr_mfb_eof_pos(i);
            tx_usr_mfb_src_rdy_int(i)   <= dma_tx_usr_mfb_src_rdy(i);
            dma_tx_usr_mfb_dst_rdy(i)   <= tx_usr_mfb_dst_rdy_int(i);
        end generate;
    end generate;

    -- =====================================================================

end architecture;
