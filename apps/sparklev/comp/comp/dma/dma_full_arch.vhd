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

    constant GLS_MI_OFFSET : std_logic_vector(32-1 downto 0) := X"0000_0200";

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

    -- =============================================================================================
    -- RX: Metadata extractor -> GLS
    -- =============================================================================================
    signal c2h_dma_mvb_data_ext    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS)) -1 downto 0);
    signal c2h_dma_mvb_vld_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mvb_src_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mvb_dst_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal c2h_dma_mfb_data_ext    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal c2h_dma_mfb_sof_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_eof_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_sof_pos_ext : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_eof_pos_ext : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_src_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mfb_dst_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- TX: GLS -> Metadata insertor
    -- =============================================================================================
    signal h2c_dma_mvb_pkt_size_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal h2c_dma_mvb_hdr_meta_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
    signal h2c_dma_mvb_chan_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(H2C_CHANNELS) -1 downto 0);
    signal h2c_dma_mvb_vld_gls      : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mvb_src_rdy_gls  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mvb_dst_rdy_gls  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal h2c_dma_mfb_data_gls    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal h2c_dma_mfb_sof_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_eof_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_sof_pos_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_eof_pos_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_src_rdy_gls : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mfb_dst_rdy_gls : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- RX: GLS -> Metadata insertor
    -- =============================================================================================
    signal c2h_dma_mvb_pkt_size_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal c2h_dma_mvb_hdr_meta_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
    signal c2h_dma_mvb_chan_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(C2H_CHANNELS) -1 downto 0);
    signal c2h_dma_mvb_vld_gls      : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mvb_src_rdy_gls  : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mvb_dst_rdy_gls  : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal c2h_dma_mfb_data_gls    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal c2h_dma_mfb_sof_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_eof_gls     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_sof_pos_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_eof_pos_gls : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_src_rdy_gls : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mfb_dst_rdy_gls : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- TX: Metadata extractor -> GLS
    -- =============================================================================================
    signal h2c_dma_mvb_data_ext    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS)) -1 downto 0);
    signal h2c_dma_mvb_vld_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mvb_src_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mvb_dst_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);

    signal h2c_dma_mfb_data_ext    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal h2c_dma_mfb_sof_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_eof_ext     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_sof_pos_ext : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_eof_pos_ext : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_src_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mfb_dst_rdy_ext : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- RX: Metadata insertor -> DMA wrapper
    -- =============================================================================================
    signal c2h_dma_mfb_meta_pkt_size_ins : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal c2h_dma_mfb_meta_hdr_meta_ins : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
    signal c2h_dma_mfb_meta_chan_ins     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(C2H_CHANNELS) -1 downto 0);

    signal c2h_dma_mfb_data_ins    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal c2h_dma_mfb_sof_ins     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_eof_ins     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_sof_pos_ins : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_eof_pos_ins : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_src_rdy_ins : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal c2h_dma_mfb_dst_rdy_ins : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- TX: DMA wrapper -> Metadata extractor
    -- =============================================================================================
    signal h2c_dma_mfb_meta_pkt_size_dma : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal h2c_dma_mfb_meta_hdr_meta_dma : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
    signal h2c_dma_mfb_meta_chan_dma     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(H2C_CHANNELS) -1 downto 0);

    signal h2c_dma_mfb_data_dma    : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal h2c_dma_mfb_sof_dma     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_eof_dma     : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_sof_pos_dma : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_eof_pos_dma : slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_src_rdy_dma : std_logic_vector(DMA_STREAMS -1 downto 0);
    signal h2c_dma_mfb_dst_rdy_dma : std_logic_vector(DMA_STREAMS -1 downto 0);

    -- =============================================================================================
    -- Miscellaneous
    -- =============================================================================================
    -- helper signal to parse the output of the metadata insertor to the output ports
    signal h2c_dma_mfb_meta_ins : slv_array_t(DMA_STREAMS -1 downto 0)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto 0);
    -- helper signal to parse metatdata on the RX interface of the DMA wrapper
    signal c2h_dma_mfb_meta_ins : slv_array_t(DMA_STREAMS -1 downto 0)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS) -1 downto 0);
begin

    -- =====================================================================
    --  DMA Module
    -- =====================================================================
    dma_wrapper_i : entity work.DMA_WRAPPER
        generic map(
            DEVICE => DEVICE,

            DMA_STREAMS => DMA_STREAMS,

            DMA_MFB_REGIONS     => DMA_MFB_REGIONS,
            DMA_MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
            DMA_MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
            DMA_MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,

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
            PKT_SIZE_MAX   => PKT_SIZE_MAX,

            C2H_CHANNELS  => C2H_CHANNELS,
            C2H_PTR_WIDTH => C2H_PTR_WIDTH,

            H2C_CHANNELS  => H2C_CHANNELS,
            H2C_PTR_WIDTH => H2C_PTR_WIDTH,

            C2H_GEN_EN => C2H_GEN_EN,
            H2C_GEN_EN => H2C_GEN_EN,

            DMA_DEBUG_ENABLE => DMA_DEBUG_ENABLE,
            MI_WIDTH         => 32
        )
        port map(
            MI_CLK   => MI_CLK,
            MI_RESET => MI_RESET,

            DMA_CLK   => DMA_CLK,
            DMA_RESET => DMA_RESET,

            C2H_DMA_MFB_META_PKT_SIZE => (others => (others => '0')),
            C2H_DMA_MFB_META_HDR_META => c2h_dma_mfb_meta_hdr_meta_ins,
            C2H_DMA_MFB_META_CHAN     => c2h_dma_mfb_meta_chan_ins,

            C2H_DMA_MFB_DATA    => c2h_dma_mfb_data_ins,
            C2H_DMA_MFB_SOF     => c2h_dma_mfb_sof_ins,
            C2H_DMA_MFB_EOF     => c2h_dma_mfb_eof_ins,
            C2H_DMA_MFB_SOF_POS => c2h_dma_mfb_sof_pos_ins,
            C2H_DMA_MFB_EOF_POS => c2h_dma_mfb_eof_pos_ins,
            C2H_DMA_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_ins,
            C2H_DMA_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_ins,

            H2C_DMA_MFB_META_PKT_SIZE => h2c_dma_mfb_meta_pkt_size_dma,
            H2C_DMA_MFB_META_HDR_META => h2c_dma_mfb_meta_hdr_meta_dma,
            H2C_DMA_MFB_META_CHAN     => h2c_dma_mfb_meta_chan_dma,

            H2C_DMA_MFB_DATA    => h2c_dma_mfb_data_dma,
            H2C_DMA_MFB_SOF     => h2c_dma_mfb_sof_dma,
            H2C_DMA_MFB_EOF     => h2c_dma_mfb_eof_dma,
            H2C_DMA_MFB_SOF_POS => h2c_dma_mfb_sof_pos_dma,
            H2C_DMA_MFB_EOF_POS => h2c_dma_mfb_eof_pos_dma,
            H2C_DMA_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_dma,
            H2C_DMA_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_dma,

            PCIE_RQ_MFB_DATA    => PCIE_RQ_MFB_DATA,
            PCIE_RQ_MFB_META    => PCIE_RQ_MFB_META,
            PCIE_RQ_MFB_SOF     => PCIE_RQ_MFB_SOF,
            PCIE_RQ_MFB_EOF     => PCIE_RQ_MFB_EOF,
            PCIE_RQ_MFB_SOF_POS => PCIE_RQ_MFB_SOF_POS,
            PCIE_RQ_MFB_EOF_POS => PCIE_RQ_MFB_EOF_POS,
            PCIE_RQ_MFB_SRC_RDY => PCIE_RQ_MFB_SRC_RDY,
            PCIE_RQ_MFB_DST_RDY => PCIE_RQ_MFB_DST_RDY,

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

    gls_mi_split_g : if (GEN_LOOP_EN) generate
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
        GEN_LOOP_MI_DRD  <= x"DEADBEAD";
        GEN_LOOP_MI_DRDY <= GEN_LOOP_MI_RD;
    end generate;

    gls_g : for stream in 0 to DMA_STREAMS-1 generate
        gls_en_g : if (GEN_LOOP_EN) generate

            c2h_dma_meta_extract_i : entity work.METADATA_EXTRACTOR
                generic map (
                    MVB_ITEMS => DMA_MFB_REGIONS,

                    MFB_REGIONS     => DMA_MFB_REGIONS,
                    MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                    MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,
                    MFB_META_WIDTH  => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS),

                    EXTRACT_MODE     => 0,
                    MVB_SHAKEDOWN_EN => TRUE,
                    OUT_MVB_PIPE_EN  => TRUE,
                    OUT_MFB_PIPE_EN  => TRUE,
                    DEVICE           => DEVICE)
                port map (
                    CLK   => DMA_CLK(stream),
                    RESET => DMA_RESET(stream),

                    RX_MFB_DATA    => C2H_DMA_MFB_DATA(stream),
                    RX_MFB_META    => (log2(PKT_SIZE_MAX+1) -1 downto 0 => '0') & C2H_DMA_MFB_META_HDR_META(stream) & C2H_DMA_MFB_META_CHAN(stream),
                    RX_MFB_SOF     => C2H_DMA_MFB_SOF(stream),
                    RX_MFB_EOF     => C2H_DMA_MFB_EOF(stream),
                    RX_MFB_SOF_POS => C2H_DMA_MFB_SOF_POS(stream),
                    RX_MFB_EOF_POS => C2H_DMA_MFB_EOF_POS(stream),
                    RX_MFB_SRC_RDY => C2H_DMA_MFB_SRC_RDY(stream),
                    RX_MFB_DST_RDY => C2H_DMA_MFB_DST_RDY(stream),

                    TX_MVB_DATA    => c2h_dma_mvb_data_ext(stream),
                    TX_MVB_VLD     => c2h_dma_mvb_vld_ext(stream),
                    TX_MVB_SRC_RDY => c2h_dma_mvb_src_rdy_ext(stream),
                    TX_MVB_DST_RDY => c2h_dma_mvb_dst_rdy_ext(stream),

                    TX_MFB_DATA    => c2h_dma_mfb_data_ext(stream),
                    TX_MFB_META    => open,
                    TX_MFB_SOF     => c2h_dma_mfb_sof_ext(stream),
                    TX_MFB_EOF     => c2h_dma_mfb_eof_ext(stream),
                    TX_MFB_SOF_POS => c2h_dma_mfb_sof_pos_ext(stream),
                    TX_MFB_EOF_POS => c2h_dma_mfb_eof_pos_ext(stream),
                    TX_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_ext(stream),
                    TX_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_ext(stream));

            h2c_dma_meta_insert_i : entity work.METADATA_INSERTOR
                generic map (
                    MVB_ITEMS      => DMA_MFB_REGIONS,
                    MVB_ITEM_WIDTH => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS),

                    MFB_REGIONS     => DMA_MFB_REGIONS,
                    MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                    MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,
                    MFB_META_WIDTH  => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS),

                    INSERT_MODE     => 0,
                    MVB_FIFO_SIZE   => 16,
                    MVB_FIFOX_MULTI => TRUE,
                    DEVICE          => DEVICE)
                port map (
                    CLK   => DMA_CLK(stream),
                    RESET => DMA_RESET(stream),

                    RX_MVB_DATA    => h2c_dma_mvb_pkt_size_gls(stream) & h2c_dma_mvb_hdr_meta_gls(stream) & h2c_dma_mvb_chan_gls(stream),
                    RX_MVB_VLD     => h2c_dma_mvb_vld_gls(stream),
                    RX_MVB_SRC_RDY => h2c_dma_mvb_src_rdy_gls(stream),
                    RX_MVB_DST_RDY => h2c_dma_mvb_dst_rdy_gls(stream),

                    RX_MFB_DATA    => h2c_dma_mfb_data_gls(stream),
                    RX_MFB_META    => (others => '0'),
                    RX_MFB_SOF     => h2c_dma_mfb_sof_gls(stream),
                    RX_MFB_EOF     => h2c_dma_mfb_eof_gls(stream),
                    RX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_gls(stream),
                    RX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_gls(stream),
                    RX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_gls(stream),
                    RX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_gls(stream),

                    TX_MFB_DATA     => H2C_DMA_MFB_DATA(stream),
                    TX_MFB_META     => open,
                    -- TODO: connect this meta signal to the output
                    TX_MFB_META_NEW => h2c_dma_mfb_meta_ins(stream),
                    TX_MFB_SOF      => H2C_DMA_MFB_SOF(stream),
                    TX_MFB_EOF      => H2C_DMA_MFB_EOF(stream),
                    TX_MFB_SOF_POS  => H2C_DMA_MFB_SOF_POS(stream),
                    TX_MFB_EOF_POS  => H2C_DMA_MFB_EOF_POS(stream),
                    TX_MFB_SRC_RDY  => H2C_DMA_MFB_SRC_RDY(stream),
                    TX_MFB_DST_RDY  => H2C_DMA_MFB_DST_RDY(stream));

            H2C_DMA_MFB_META_PKT_SIZE(stream) <= h2c_dma_mfb_meta_ins(stream)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto HDR_META_WIDTH + log2(H2C_CHANNELS));
            H2C_DMA_MFB_META_HDR_META(stream) <= h2c_dma_mfb_meta_ins(stream)(HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto log2(H2C_CHANNELS));
            H2C_DMA_MFB_META_CHAN(stream)     <= h2c_dma_mfb_meta_ins(stream)(log2(H2C_CHANNELS) -1 downto 0);

            gen_loop_switch_i : entity work.GEN_LOOP_SWITCH
                generic map(
                    REGIONS           => DMA_MFB_REGIONS,
                    REGION_SIZE       => DMA_MFB_REGION_SIZE,
                    BLOCK_SIZE        => DMA_MFB_BLOCK_SIZE,
                    ITEM_WIDTH        => DMA_MFB_ITEM_WIDTH,
                    PKT_MTU           => PKT_SIZE_MAX,
                    RX_DMA_CHANNELS   => C2H_CHANNELS,
                    TX_DMA_CHANNELS   => H2C_CHANNELS,
                    HDR_META_WIDTH    => HDR_META_WIDTH,
                    PLAYER_FIFO_DEPTH => 512,
                    RX_HDR_INS_EN     => FALSE,
                    SAME_CLK          => FALSE,
                    MI_PIPE_EN        => TRUE,
                    FAKE_SWITCH       => FALSE,
                    DEVICE            => DEVICE
                )
                port map(
                    MI_CLK   => MI_CLK,
                    MI_RESET => MI_RESET,
                    MI_DWR   => gls_mi_dwr(stream),
                    MI_ADDR  => gls_mi_addr(stream),
                    MI_BE    => gls_mi_be(stream),
                    MI_RD    => gls_mi_rd(stream),
                    MI_WR    => gls_mi_wr(stream),
                    MI_ARDY  => gls_mi_ardy(stream),
                    MI_DRD   => gls_mi_drd(stream),
                    MI_DRDY  => gls_mi_drdy(stream),

                    CLK   => DMA_CLK(stream),
                    RESET => DMA_RESET(stream),

                    ETH_RX_MVB_LEN      => c2h_dma_mvb_data_ext(stream)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS) -1 downto HDR_META_WIDTH + log2(C2H_CHANNELS)),
                    ETH_RX_MVB_HDR_META => c2h_dma_mvb_data_ext(stream)(HDR_META_WIDTH + log2(C2H_CHANNELS) -1 downto log2(C2H_CHANNELS)),
                    ETH_RX_MVB_CHANNEL  => c2h_dma_mvb_data_ext(stream)(log2(C2H_CHANNELS) -1 downto 0),
                    ETH_RX_MVB_DISCARD  => (others => '0'),
                    ETH_RX_MVB_VLD      => c2h_dma_mvb_vld_ext(stream),
                    ETH_RX_MVB_SRC_RDY  => c2h_dma_mvb_src_rdy_ext(stream),
                    ETH_RX_MVB_DST_RDY  => c2h_dma_mvb_dst_rdy_ext(stream),

                    ETH_RX_MFB_DATA    => c2h_dma_mfb_data_ext(stream),
                    ETH_RX_MFB_SOF     => c2h_dma_mfb_sof_ext(stream),
                    ETH_RX_MFB_EOF     => c2h_dma_mfb_eof_ext(stream),
                    ETH_RX_MFB_SOF_POS => c2h_dma_mfb_sof_pos_ext(stream),
                    ETH_RX_MFB_EOF_POS => c2h_dma_mfb_eof_pos_ext(stream),
                    ETH_RX_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_ext(stream),
                    ETH_RX_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_ext(stream),

                    ETH_TX_MVB_LEN      => h2c_dma_mvb_pkt_size_gls(stream),
                    ETH_TX_MVB_HDR_META => h2c_dma_mvb_hdr_meta_gls(stream),
                    ETH_TX_MVB_CHANNEL  => h2c_dma_mvb_chan_gls(stream),
                    ETH_TX_MVB_VLD      => h2c_dma_mvb_vld_gls(stream),
                    ETH_TX_MVB_SRC_RDY  => h2c_dma_mvb_src_rdy_gls(stream),
                    ETH_TX_MVB_DST_RDY  => h2c_dma_mvb_dst_rdy_gls(stream),

                    ETH_TX_MFB_DATA    => h2c_dma_mfb_data_gls(stream),
                    ETH_TX_MFB_SOF     => h2c_dma_mfb_sof_gls(stream),
                    ETH_TX_MFB_EOF     => h2c_dma_mfb_eof_gls(stream),
                    ETH_TX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_gls(stream),
                    ETH_TX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_gls(stream),
                    ETH_TX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_gls(stream),
                    ETH_TX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_gls(stream),

                    DMA_RX_MVB_LEN      => c2h_dma_mvb_pkt_size_gls(stream),
                    DMA_RX_MVB_HDR_META => c2h_dma_mvb_hdr_meta_gls(stream),
                    DMA_RX_MVB_CHANNEL  => c2h_dma_mvb_chan_gls(stream),
                    DMA_RX_MVB_DISCARD  => open,
                    DMA_RX_MVB_VLD      => c2h_dma_mvb_vld_gls(stream),
                    DMA_RX_MVB_SRC_RDY  => c2h_dma_mvb_src_rdy_gls(stream),
                    DMA_RX_MVB_DST_RDY  => c2h_dma_mvb_dst_rdy_gls(stream),

                    DMA_RX_MFB_DATA    => c2h_dma_mfb_data_gls(stream),
                    DMA_RX_MFB_SOF     => c2h_dma_mfb_sof_gls(stream),
                    DMA_RX_MFB_EOF     => c2h_dma_mfb_eof_gls(stream),
                    DMA_RX_MFB_SOF_POS => c2h_dma_mfb_sof_pos_gls(stream),
                    DMA_RX_MFB_EOF_POS => c2h_dma_mfb_eof_pos_gls(stream),
                    DMA_RX_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_gls(stream),
                    DMA_RX_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_gls(stream),

                    DMA_TX_MVB_LEN      => h2c_dma_mvb_data_ext(stream)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto HDR_META_WIDTH + log2(H2C_CHANNELS)),
                    DMA_TX_MVB_HDR_META => h2c_dma_mvb_data_ext(stream)(HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto log2(H2C_CHANNELS)),
                    DMA_TX_MVB_CHANNEL  => h2c_dma_mvb_data_ext(stream)(log2(H2C_CHANNELS) -1 downto 0),
                    DMA_TX_MVB_VLD      => h2c_dma_mvb_vld_ext(stream),
                    DMA_TX_MVB_SRC_RDY  => h2c_dma_mvb_src_rdy_ext(stream),
                    DMA_TX_MVB_DST_RDY  => h2c_dma_mvb_dst_rdy_ext(stream),

                    DMA_TX_MFB_DATA    => h2c_dma_mfb_data_ext(stream),
                    DMA_TX_MFB_SOF     => h2c_dma_mfb_sof_ext(stream),
                    DMA_TX_MFB_EOF     => h2c_dma_mfb_eof_ext(stream),
                    DMA_TX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_ext(stream),
                    DMA_TX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_ext(stream),
                    DMA_TX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_ext(stream),
                    DMA_TX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_ext(stream)
                );

            c2h_dma_meta_insert_i : entity work.METADATA_INSERTOR
                generic map (
                    MVB_ITEMS      => DMA_MFB_REGIONS,
                    MVB_ITEM_WIDTH => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS),

                    MFB_REGIONS     => DMA_MFB_REGIONS,
                    MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                    MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,
                    MFB_META_WIDTH  => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS),

                    INSERT_MODE     => 0,
                    MVB_FIFO_SIZE   => 16,
                    MVB_FIFOX_MULTI => TRUE,
                    DEVICE          => DEVICE)
                port map (
                    CLK   => DMA_CLK(stream),
                    RESET => DMA_RESET(stream),

                    RX_MVB_DATA    => c2h_dma_mvb_pkt_size_gls(stream) & c2h_dma_mvb_hdr_meta_gls(stream) & c2h_dma_mvb_chan_gls(stream),
                    RX_MVB_VLD     => c2h_dma_mvb_vld_gls(stream),
                    RX_MVB_SRC_RDY => c2h_dma_mvb_src_rdy_gls(stream),
                    RX_MVB_DST_RDY => c2h_dma_mvb_dst_rdy_gls(stream),

                    RX_MFB_DATA    => c2h_dma_mfb_data_gls(stream),
                    RX_MFB_META    => (others => '0'),
                    RX_MFB_SOF     => c2h_dma_mfb_sof_gls(stream),
                    RX_MFB_EOF     => c2h_dma_mfb_eof_gls(stream),
                    RX_MFB_SOF_POS => c2h_dma_mfb_sof_pos_gls(stream),
                    RX_MFB_EOF_POS => c2h_dma_mfb_eof_pos_gls(stream),
                    RX_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_gls(stream),
                    RX_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_gls(stream),

                    TX_MFB_DATA     => c2h_dma_mfb_data_ins(stream),
                    TX_MFB_META     => open,
                    TX_MFB_META_NEW => c2h_dma_mfb_meta_ins(stream),
                    TX_MFB_SOF      => c2h_dma_mfb_sof_ins(stream),
                    TX_MFB_EOF      => c2h_dma_mfb_eof_ins(stream),
                    TX_MFB_SOF_POS  => c2h_dma_mfb_sof_pos_ins(stream),
                    TX_MFB_EOF_POS  => c2h_dma_mfb_eof_pos_ins(stream),
                    TX_MFB_SRC_RDY  => c2h_dma_mfb_src_rdy_ins(stream),
                    TX_MFB_DST_RDY  => c2h_dma_mfb_dst_rdy_ins(stream));

            c2h_dma_mfb_meta_pkt_size_ins(stream) <= c2h_dma_mfb_meta_ins(stream)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(C2H_CHANNELS) -1 downto HDR_META_WIDTH + log2(C2H_CHANNELS));
            c2h_dma_mfb_meta_hdr_meta_ins(stream) <= c2h_dma_mfb_meta_ins(stream)(HDR_META_WIDTH + log2(C2H_CHANNELS) -1 downto log2(C2H_CHANNELS));
            c2h_dma_mfb_meta_chan_ins(stream)     <= c2h_dma_mfb_meta_ins(stream)(log2(C2H_CHANNELS) -1 downto 0);

            h2c_dma_meta_extract_i : entity work.METADATA_EXTRACTOR
                generic map (
                    MVB_ITEMS => DMA_MFB_REGIONS,

                    MFB_REGIONS     => DMA_MFB_REGIONS,
                    MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                    MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                    MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,
                    MFB_META_WIDTH  => log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS),

                    EXTRACT_MODE     => 0,
                    MVB_SHAKEDOWN_EN => TRUE,
                    OUT_MVB_PIPE_EN  => TRUE,
                    OUT_MFB_PIPE_EN  => TRUE,
                    DEVICE           => DEVICE)
                port map (
                    CLK   => DMA_CLK(stream),
                    RESET => DMA_RESET(stream),

                    RX_MFB_DATA    => h2c_dma_mfb_data_dma(stream),
                    RX_MFB_META    => h2c_dma_mfb_meta_pkt_size_dma(stream) & h2c_dma_mfb_meta_hdr_meta_dma(stream) & h2c_dma_mfb_meta_chan_dma(stream),
                    RX_MFB_SOF     => h2c_dma_mfb_sof_dma(stream),
                    RX_MFB_EOF     => h2c_dma_mfb_eof_dma(stream),
                    RX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_dma(stream),
                    RX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_dma(stream),
                    RX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_dma(stream),
                    RX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_dma(stream),

                    TX_MVB_DATA    => h2c_dma_mvb_data_ext(stream),
                    TX_MVB_VLD     => h2c_dma_mvb_vld_ext(stream),
                    TX_MVB_SRC_RDY => h2c_dma_mvb_src_rdy_ext(stream),
                    TX_MVB_DST_RDY => h2c_dma_mvb_dst_rdy_ext(stream),

                    TX_MFB_DATA    => h2c_dma_mfb_data_ext(stream),
                    TX_MFB_META    => open,
                    TX_MFB_SOF     => h2c_dma_mfb_sof_ext(stream),
                    TX_MFB_EOF     => h2c_dma_mfb_eof_ext(stream),
                    TX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_ext(stream),
                    TX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_ext(stream),
                    TX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_ext(stream),
                    TX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_ext(stream));

        else generate
            c2h_dma_mfb_meta_pkt_size_ins(stream) <= (others => '0');
            c2h_dma_mfb_meta_hdr_meta_ins(stream) <= C2H_DMA_MFB_META_HDR_META(stream);
            c2h_dma_mfb_meta_chan_ins(stream)     <= C2H_DMA_MFB_META_CHAN(stream);

            c2h_dma_mfb_data_ins(stream)    <= C2H_DMA_MFB_DATA(stream);
            c2h_dma_mfb_sof_ins(stream)     <= C2H_DMA_MFB_SOF(stream);
            c2h_dma_mfb_eof_ins(stream)     <= C2H_DMA_MFB_EOF(stream);
            c2h_dma_mfb_sof_pos_ins(stream) <= C2H_DMA_MFB_SOF_POS(stream);
            c2h_dma_mfb_eof_pos_ins(stream) <= C2H_DMA_MFB_EOF_POS(stream);
            c2h_dma_mfb_src_rdy_ins(stream) <= C2H_DMA_MFB_SRC_RDY(stream);
            C2H_DMA_MFB_DST_RDY(stream)     <= c2h_dma_mfb_dst_rdy_ins(stream);

            H2C_DMA_MFB_META_PKT_SIZE(stream) <= h2c_dma_mfb_meta_pkt_size_dma(stream);
            H2C_DMA_MFB_META_HDR_META(stream) <= h2c_dma_mfb_meta_hdr_meta_dma(stream);
            H2C_DMA_MFB_META_CHAN(stream)     <= h2c_dma_mfb_meta_chan_dma(stream);

            H2C_DMA_MFB_DATA(stream)        <= h2c_dma_mfb_data_dma(stream);
            H2C_DMA_MFB_SOF(stream)         <= h2c_dma_mfb_sof_dma(stream);
            H2C_DMA_MFB_EOF(stream)         <= h2c_dma_mfb_eof_dma(stream);
            H2C_DMA_MFB_SOF_POS(stream)     <= h2c_dma_mfb_sof_pos_dma(stream);
            H2C_DMA_MFB_EOF_POS(stream)     <= h2c_dma_mfb_eof_pos_dma(stream);
            H2C_DMA_MFB_SRC_RDY(stream)     <= h2c_dma_mfb_src_rdy_dma(stream);
            h2c_dma_mfb_dst_rdy_dma(stream) <= H2C_DMA_MFB_DST_RDY(stream);
        end generate;
    end generate;
end architecture;
