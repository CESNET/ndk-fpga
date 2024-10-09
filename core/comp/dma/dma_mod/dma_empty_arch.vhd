-- dma_empty.vhd: DMA Empty Wrapper
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture EMPTY of DMA is

    constant GLS_MI_OFFSET     : std_logic_vector(32-1 downto 0) := X"0000_0100";
    constant IUSR_MVB_ITEMS    : natural := tsel(DMA_400G_DEMO,4,USR_MVB_ITEMS);
    constant IUSR_MFB_REGIONS  : natural := tsel(DMA_400G_DEMO,4,USR_MFB_REGIONS);

    function gls_mi_addr_base_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(DMA_STREAMS-1 downto 0)(32-1 downto 0);
    begin
        for i in 0 to DMA_STREAMS-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(GLS_MI_OFFSET), 32));
        end loop;
        return mi_addr_base_var;
    end function;

    -- =====================================================================
    --  MI Splitting
    -- =====================================================================

    signal gls_mi_addr  : slv_array_t     (DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal gls_mi_dwr   : slv_array_t     (DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal gls_mi_be    : slv_array_t     (DMA_STREAMS-1 downto 0)(32/8-1 downto 0);
    signal gls_mi_rd    : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal gls_mi_wr    : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal gls_mi_drd   : slv_array_t     (DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal gls_mi_ardy  : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal gls_mi_drdy  : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =====================================================================

    signal rx_usr_arr_mvb_len       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1)-1 downto 0);
    signal rx_usr_arr_mvb_hdr_meta  : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH          -1 downto 0);
    signal rx_usr_arr_mvb_channel   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(RX_CHANNELS)       -1 downto 0);
    signal rx_usr_arr_mvb_discard   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*1                       -1 downto 0);
    signal rx_usr_arr_mvb_vld       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS                         -1 downto 0);
    signal rx_usr_arr_mvb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal rx_usr_arr_mvb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal rx_usr_arr_mfb_data      : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal rx_usr_arr_mfb_sof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal rx_usr_arr_mfb_eof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal rx_usr_arr_mfb_sof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE))                         -1 downto 0);
    signal rx_usr_arr_mfb_eof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE))      -1 downto 0);
    signal rx_usr_arr_mfb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal rx_usr_arr_mfb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal tx_usr_arr_mvb_len       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(USR_TX_PKT_SIZE_MAX+1)-1 downto 0);
    signal tx_usr_arr_mvb_hdr_meta  : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH          -1 downto 0);
    signal tx_usr_arr_mvb_channel   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(TX_CHANNELS)       -1 downto 0);
    signal tx_usr_arr_mvb_vld       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS                         -1 downto 0);
    signal tx_usr_arr_mvb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal tx_usr_arr_mvb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal tx_usr_arr_mfb_data      : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal tx_usr_arr_mfb_sof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal tx_usr_arr_mfb_eof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal tx_usr_arr_mfb_sof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE))                         -1 downto 0);
    signal tx_usr_arr_mfb_eof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE))      -1 downto 0);
    signal tx_usr_arr_mfb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal tx_usr_arr_mfb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =====================================================================
    --  GEN_LOOP_SWITCH -> DMA Module interface
    -- =====================================================================

    signal dma_rx_usr_mvb_len       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(USR_RX_PKT_SIZE_MAX+1)-1 downto 0);
    signal dma_rx_usr_mvb_hdr_meta  : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH          -1 downto 0);
    signal dma_rx_usr_mvb_channel   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(RX_CHANNELS)       -1 downto 0);
    signal dma_rx_usr_mvb_discard   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*1                       -1 downto 0);
    signal dma_rx_usr_mvb_vld       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS                         -1 downto 0);
    signal dma_rx_usr_mvb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_rx_usr_mvb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal dma_rx_usr_mfb_data      : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rx_usr_mfb_sof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal dma_rx_usr_mfb_eof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal dma_rx_usr_mfb_sof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE))                         -1 downto 0);
    signal dma_rx_usr_mfb_eof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE))      -1 downto 0);
    signal dma_rx_usr_mfb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_rx_usr_mfb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =====================================================================

    -- =====================================================================
    --  DMA Module -> GEN_LOOP_SWITCH interface
    -- =====================================================================

    signal dma_tx_usr_mvb_len       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(USR_TX_PKT_SIZE_MAX+1)-1 downto 0);
    signal dma_tx_usr_mvb_hdr_meta  : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*HDR_META_WIDTH          -1 downto 0);
    signal dma_tx_usr_mvb_channel   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS*log2(TX_CHANNELS)       -1 downto 0);
    signal dma_tx_usr_mvb_vld       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MVB_ITEMS                         -1 downto 0);
    signal dma_tx_usr_mvb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_tx_usr_mvb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal dma_tx_usr_mfb_data      : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
    signal dma_tx_usr_mfb_sof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal dma_tx_usr_mfb_eof       : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS                                                          -1 downto 0);
    signal dma_tx_usr_mfb_sof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE))                         -1 downto 0);
    signal dma_tx_usr_mfb_eof_pos   : slv_array_t(DMA_STREAMS-1 downto 0)(IUSR_MFB_REGIONS*max(1,log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE))      -1 downto 0);
    signal dma_tx_usr_mfb_src_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_tx_usr_mfb_dst_rdy   : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =====================================================================

begin

    assert ((USR_RX_PKT_SIZE_MAX = USR_TX_PKT_SIZE_MAX) or (not GEN_LOOP_EN))
        report "DMA: The maximum frame size for RX/TX DMA must be the same or the GLS module must be disabled!"
        severity failure;

    MI_ARDY <= (others => '1');
    MI_DRD  <= (others => (others => '0'));
    MI_DRDY <= (others => '0');

    PCIE_RQ_MVB_SRC_RDY <= (others => '0');
    PCIE_RQ_MFB_SRC_RDY <= (others => '0');
    PCIE_RC_MVB_DST_RDY <= (others => '1');
    PCIE_RC_MFB_DST_RDY <= (others => '1');

    -- =====================================================================
    --  DMA USER INPUT PACK/UNPACK
    -- =====================================================================

    rx_usr_arr_mvb_len      <= RX_USR_MVB_LEN;
    rx_usr_arr_mvb_hdr_meta <= RX_USR_MVB_HDR_META;
    rx_usr_arr_mvb_channel  <= RX_USR_MVB_CHANNEL;
    rx_usr_arr_mvb_discard  <= RX_USR_MVB_DISCARD;
    rx_usr_arr_mvb_vld      <= RX_USR_MVB_VLD;
    rx_usr_arr_mvb_src_rdy  <= RX_USR_MVB_SRC_RDY;
    RX_USR_MVB_DST_RDY      <= rx_usr_arr_mvb_dst_rdy;
    
    rx_usr_arr_mfb_data     <= RX_USR_MFB_DATA;
    rx_usr_arr_mfb_sof      <= RX_USR_MFB_SOF;
    rx_usr_arr_mfb_eof      <= RX_USR_MFB_EOF;
    rx_usr_arr_mfb_sof_pos  <= RX_USR_MFB_SOF_POS;
    rx_usr_arr_mfb_eof_pos  <= RX_USR_MFB_EOF_POS;
    rx_usr_arr_mfb_src_rdy  <= RX_USR_MFB_SRC_RDY;
    RX_USR_MFB_DST_RDY      <= rx_usr_arr_mfb_dst_rdy;

    TX_USR_MVB_LEN          <= tx_usr_arr_mvb_len;
    TX_USR_MVB_HDR_META     <= tx_usr_arr_mvb_hdr_meta;
    TX_USR_MVB_CHANNEL      <= tx_usr_arr_mvb_channel;
    TX_USR_MVB_VLD          <= tx_usr_arr_mvb_vld;
    TX_USR_MVB_SRC_RDY      <= tx_usr_arr_mvb_src_rdy;
    tx_usr_arr_mvb_dst_rdy  <= TX_USR_MVB_DST_RDY;

    TX_USR_MFB_DATA         <= tx_usr_arr_mfb_data;
    TX_USR_MFB_SOF          <= tx_usr_arr_mfb_sof;
    TX_USR_MFB_EOF          <= tx_usr_arr_mfb_eof;
    TX_USR_MFB_SOF_POS      <= tx_usr_arr_mfb_sof_pos;
    TX_USR_MFB_EOF_POS      <= tx_usr_arr_mfb_eof_pos;
    TX_USR_MFB_SRC_RDY      <= tx_usr_arr_mfb_src_rdy;
    tx_usr_arr_mfb_dst_rdy  <= TX_USR_MFB_DST_RDY;

    -- =====================================================================
    --  DMA Loopback
    -- =====================================================================

    dma_tx_usr_mvb_len      <= dma_rx_usr_mvb_len;
    dma_tx_usr_mvb_hdr_meta <= dma_rx_usr_mvb_hdr_meta;
    dma_tx_usr_mvb_channel  <= dma_rx_usr_mvb_channel;
    dma_tx_usr_mvb_vld      <= dma_rx_usr_mvb_vld;
    dma_tx_usr_mvb_src_rdy  <= dma_rx_usr_mvb_src_rdy;
    dma_rx_usr_mvb_dst_rdy  <= dma_tx_usr_mvb_dst_rdy;

    dma_tx_usr_mfb_data    <= dma_rx_usr_mfb_data;
    dma_tx_usr_mfb_sof     <= dma_rx_usr_mfb_sof;
    dma_tx_usr_mfb_eof     <= dma_rx_usr_mfb_eof;
    dma_tx_usr_mfb_sof_pos <= dma_rx_usr_mfb_sof_pos;
    dma_tx_usr_mfb_eof_pos <= dma_rx_usr_mfb_eof_pos;
    dma_tx_usr_mfb_src_rdy <= dma_rx_usr_mfb_src_rdy;
    dma_rx_usr_mfb_dst_rdy <= dma_tx_usr_mfb_dst_rdy;

    -- =====================================================================
    --  GLS Module
    -- =====================================================================

    mi_splitter_gls_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH  => 32,
        DATA_WIDTH  => 32,
        META_WIDTH  => 0,
        PORTS       => DMA_STREAMS,
        ADDR_BASE   => gls_mi_addr_base_f,
        DEVICE      => DEVICE
    )
    port map(
        CLK         => MI_CLK,
        RESET       => MI_RESET,

        RX_DWR      => GEN_LOOP_MI_DWR,
        RX_ADDR     => GEN_LOOP_MI_ADDR,
        RX_BE       => GEN_LOOP_MI_BE,
        RX_RD       => GEN_LOOP_MI_RD,
        RX_WR       => GEN_LOOP_MI_WR,
        RX_ARDY     => GEN_LOOP_MI_ARDY,
        RX_DRD      => GEN_LOOP_MI_DRD,
        RX_DRDY     => GEN_LOOP_MI_DRDY,

        TX_DWR      => gls_mi_dwr,
        TX_ADDR     => gls_mi_addr,
        TX_BE       => gls_mi_be,
        TX_RD       => gls_mi_rd,
        TX_WR       => gls_mi_wr,
        TX_ARDY     => gls_mi_ardy,
        TX_DRD      => gls_mi_drd,
        TX_DRDY     => gls_mi_drdy
    );

    gls_g : for i in 0 to DMA_STREAMS-1 generate
        gls_en_g : if (GEN_LOOP_EN) generate
            gen_loop_switch_i : entity work.GEN_LOOP_SWITCH
            generic map(
                REGIONS           => IUSR_MFB_REGIONS    ,
                REGION_SIZE       => USR_MFB_REGION_SIZE,
                BLOCK_SIZE        => USR_MFB_BLOCK_SIZE ,
                ITEM_WIDTH        => USR_MFB_ITEM_WIDTH ,
                PKT_MTU           => USR_RX_PKT_SIZE_MAX,
                RX_DMA_CHANNELS   => RX_CHANNELS        ,
                TX_DMA_CHANNELS   => TX_CHANNELS        ,
                HDR_META_WIDTH    => HDR_META_WIDTH     ,
                RX_HDR_INS_EN     => false              , -- only enable for version 1 to DMA Medusa
                SAME_CLK          => false              ,
                MI_PIPE_EN        => true               ,
                DEVICE            => DEVICE
            ) 
            port map(
                MI_CLK              => MI_CLK,
                MI_RESET            => MI_RESET,
                MI_DWR              => gls_mi_dwr(i),
                MI_ADDR             => gls_mi_addr(i),
                MI_BE               => gls_mi_be(i),
                MI_RD               => gls_mi_rd(i),
                MI_WR               => gls_mi_wr(i),
                MI_ARDY             => gls_mi_ardy(i),
                MI_DRD              => gls_mi_drd(i),
                MI_DRDY             => gls_mi_drdy(i),

                CLK                 => USR_CLK                ,
                RESET               => USR_RESET              ,

                ETH_RX_MVB_LEN      => rx_usr_arr_mvb_len(i)     ,
                ETH_RX_MVB_HDR_META => rx_usr_arr_mvb_hdr_meta(i),
                ETH_RX_MVB_CHANNEL  => rx_usr_arr_mvb_channel(i) ,
                ETH_RX_MVB_DISCARD  => rx_usr_arr_mvb_discard(i) ,
                ETH_RX_MVB_VLD      => rx_usr_arr_mvb_vld(i)     ,
                ETH_RX_MVB_SRC_RDY  => rx_usr_arr_mvb_src_rdy(i) ,
                ETH_RX_MVB_DST_RDY  => rx_usr_arr_mvb_dst_rdy(i) ,

                ETH_RX_MFB_DATA     => rx_usr_arr_mfb_data(i)    ,
                ETH_RX_MFB_SOF      => rx_usr_arr_mfb_sof(i)     ,
                ETH_RX_MFB_EOF      => rx_usr_arr_mfb_eof(i)     ,
                ETH_RX_MFB_SOF_POS  => rx_usr_arr_mfb_sof_pos(i) ,
                ETH_RX_MFB_EOF_POS  => rx_usr_arr_mfb_eof_pos(i) ,
                ETH_RX_MFB_SRC_RDY  => rx_usr_arr_mfb_src_rdy(i) ,
                ETH_RX_MFB_DST_RDY  => rx_usr_arr_mfb_dst_rdy(i) ,

                ETH_TX_MVB_LEN      => tx_usr_arr_mvb_len(i)     ,
                ETH_TX_MVB_HDR_META => tx_usr_arr_mvb_hdr_meta(i),
                ETH_TX_MVB_CHANNEL  => tx_usr_arr_mvb_channel(i) ,
                ETH_TX_MVB_VLD      => tx_usr_arr_mvb_vld(i)     ,
                ETH_TX_MVB_SRC_RDY  => tx_usr_arr_mvb_src_rdy(i) ,
                ETH_TX_MVB_DST_RDY  => tx_usr_arr_mvb_dst_rdy(i) ,

                ETH_TX_MFB_DATA     => tx_usr_arr_mfb_data(i)    ,
                ETH_TX_MFB_SOF      => tx_usr_arr_mfb_sof(i)     ,
                ETH_TX_MFB_EOF      => tx_usr_arr_mfb_eof(i)     ,
                ETH_TX_MFB_SOF_POS  => tx_usr_arr_mfb_sof_pos(i) ,
                ETH_TX_MFB_EOF_POS  => tx_usr_arr_mfb_eof_pos(i) ,
                ETH_TX_MFB_SRC_RDY  => tx_usr_arr_mfb_src_rdy(i) ,
                ETH_TX_MFB_DST_RDY  => tx_usr_arr_mfb_dst_rdy(i) ,

                DMA_RX_MVB_LEN      => dma_rx_usr_mvb_len(i)     ,
                DMA_RX_MVB_HDR_META => dma_rx_usr_mvb_hdr_meta(i),
                DMA_RX_MVB_CHANNEL  => dma_rx_usr_mvb_channel(i) ,
                DMA_RX_MVB_DISCARD  => dma_rx_usr_mvb_discard(i) ,
                DMA_RX_MVB_VLD      => dma_rx_usr_mvb_vld(i)     ,
                DMA_RX_MVB_SRC_RDY  => dma_rx_usr_mvb_src_rdy(i) ,
                DMA_RX_MVB_DST_RDY  => dma_rx_usr_mvb_dst_rdy(i) ,

                DMA_RX_MFB_DATA     => dma_rx_usr_mfb_data(i)    ,
                DMA_RX_MFB_SOF      => dma_rx_usr_mfb_sof(i)     ,
                DMA_RX_MFB_EOF      => dma_rx_usr_mfb_eof(i)     ,
                DMA_RX_MFB_SOF_POS  => dma_rx_usr_mfb_sof_pos(i) ,
                DMA_RX_MFB_EOF_POS  => dma_rx_usr_mfb_eof_pos(i) ,
                DMA_RX_MFB_SRC_RDY  => dma_rx_usr_mfb_src_rdy(i) ,
                DMA_RX_MFB_DST_RDY  => dma_rx_usr_mfb_dst_rdy(i) ,

                DMA_TX_MVB_LEN      => dma_tx_usr_mvb_len(i)     ,
                DMA_TX_MVB_HDR_META => dma_tx_usr_mvb_hdr_meta(i),
                DMA_TX_MVB_CHANNEL  => dma_tx_usr_mvb_channel(i) ,
                DMA_TX_MVB_VLD      => dma_tx_usr_mvb_vld(i)     ,
                DMA_TX_MVB_SRC_RDY  => dma_tx_usr_mvb_src_rdy(i) ,
                DMA_TX_MVB_DST_RDY  => dma_tx_usr_mvb_dst_rdy(i) ,
                
                DMA_TX_MFB_DATA     => dma_tx_usr_mfb_data(i)    ,
                DMA_TX_MFB_SOF      => dma_tx_usr_mfb_sof(i)     ,
                DMA_TX_MFB_EOF      => dma_tx_usr_mfb_eof(i)     ,
                DMA_TX_MFB_SOF_POS  => dma_tx_usr_mfb_sof_pos(i) ,
                DMA_TX_MFB_EOF_POS  => dma_tx_usr_mfb_eof_pos(i) ,
                DMA_TX_MFB_SRC_RDY  => dma_tx_usr_mfb_src_rdy(i) ,
                DMA_TX_MFB_DST_RDY  => dma_tx_usr_mfb_dst_rdy(i)
            );
        else generate
            dma_rx_usr_mvb_len(i)      <= rx_usr_arr_mvb_len(i)     ;
            dma_rx_usr_mvb_hdr_meta(i) <= rx_usr_arr_mvb_hdr_meta(i);
            dma_rx_usr_mvb_channel(i)  <= rx_usr_arr_mvb_channel(i) ;
            dma_rx_usr_mvb_discard(i)  <= rx_usr_arr_mvb_discard(i) ;
            dma_rx_usr_mvb_vld(i)      <= rx_usr_arr_mvb_vld(i)     ;
            dma_rx_usr_mvb_src_rdy(i)  <= rx_usr_arr_mvb_src_rdy(i) ;
            rx_usr_arr_mvb_dst_rdy(i)  <= dma_rx_usr_mvb_dst_rdy(i) ;
            dma_rx_usr_mfb_data(i)     <= rx_usr_arr_mfb_data(i)    ;
            dma_rx_usr_mfb_sof(i)      <= rx_usr_arr_mfb_sof(i)     ;
            dma_rx_usr_mfb_eof(i)      <= rx_usr_arr_mfb_eof(i)     ;
            dma_rx_usr_mfb_sof_pos(i)  <= rx_usr_arr_mfb_sof_pos(i) ;
            dma_rx_usr_mfb_eof_pos(i)  <= rx_usr_arr_mfb_eof_pos(i) ;
            dma_rx_usr_mfb_src_rdy(i)  <= rx_usr_arr_mfb_src_rdy(i) ;
            rx_usr_arr_mfb_dst_rdy(i)  <= dma_rx_usr_mfb_dst_rdy(i) ;
            tx_usr_arr_mvb_len(i)      <= dma_tx_usr_mvb_len(i)     ;
            tx_usr_arr_mvb_hdr_meta(i) <= dma_tx_usr_mvb_hdr_meta(i);
            tx_usr_arr_mvb_channel(i)  <= dma_tx_usr_mvb_channel(i) ;
            tx_usr_arr_mvb_vld(i)      <= dma_tx_usr_mvb_vld(i)     ;
            tx_usr_arr_mvb_src_rdy(i)  <= dma_tx_usr_mvb_src_rdy(i) ;
            dma_tx_usr_mvb_dst_rdy(i)  <= tx_usr_arr_mvb_dst_rdy(i) ;
            tx_usr_arr_mfb_data(i)     <= dma_tx_usr_mfb_data(i)    ;
            tx_usr_arr_mfb_sof(i)      <= dma_tx_usr_mfb_sof(i)     ;
            tx_usr_arr_mfb_eof(i)      <= dma_tx_usr_mfb_eof(i)     ;
            tx_usr_arr_mfb_sof_pos(i)  <= dma_tx_usr_mfb_sof_pos(i) ;
            tx_usr_arr_mfb_eof_pos(i)  <= dma_tx_usr_mfb_eof_pos(i) ;
            tx_usr_arr_mfb_src_rdy(i)  <= dma_tx_usr_mfb_src_rdy(i) ;
            dma_tx_usr_mfb_dst_rdy(i)  <= tx_usr_arr_mfb_dst_rdy(i) ;

            gls_mi_ardy(i) <= gls_mi_rd(i) or gls_mi_wr(i);
            gls_mi_drd(i)  <= (others => '0');
            gls_mi_drdy(i) <= gls_mi_rd(i);
        end generate;
    end generate;

    -- =====================================================================

end architecture;
