-- application_core.vhd: User application core
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;

architecture FULL of APPLICATION_CORE is
    signal dma_rx_mvb_data_all          : std_logic_vector(log2(DMA_RX_FRAME_SIZE_MAX + 1) + DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS) -1 downto 0);
    signal dma_rx_mfb_meta_pkt_size_ext : std_logic_vector(log2(DMA_RX_FRAME_SIZE_MAX + 1) -1 downto 0);
    signal dma_rx_mfb_meta_hdr_meta_ext : std_logic_vector(DMA_HDR_META_WIDTH -1 downto 0);
    signal dma_rx_mfb_meta_chan_ext     : std_logic_vector(log2(DMA_RX_CHANNELS) -1 downto 0);

    signal dma_rx_mfb_data_ext    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rx_mfb_sof_pos_ext : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REG_SIZE))-1 downto 0);
    signal dma_rx_mfb_eof_pos_ext : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_rx_mfb_sof_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dma_rx_mfb_eof_ext     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dma_rx_mfb_src_rdy_ext : std_logic;
    signal dma_rx_mfb_dst_rdy_ext : std_logic;

    signal dma_tx_mfb_data_ins    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dma_tx_mfb_meta_ins    : std_logic_vector(log2(DMA_TX_FRAME_SIZE_MAX + 1) + DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS) -1 downto 0);
    signal dma_tx_mfb_sof_pos_ins : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REG_SIZE))-1 downto 0);
    signal dma_tx_mfb_eof_pos_ins : std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_tx_mfb_sof_ins     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dma_tx_mfb_eof_ins     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dma_tx_mfb_src_rdy_ins : std_logic;
    signal dma_tx_mfb_dst_rdy_ins : std_logic;

    signal sync_mi_dwr  : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_addr : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal sync_mi_be   : std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    signal sync_mi_rd   : std_logic;
    signal sync_mi_wr   : std_logic;
    signal sync_mi_drd  : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_ardy : std_logic;
    signal sync_mi_drdy : std_logic;
begin

    assert (ETH_STREAMS = 1 and DMA_STREAMS = 1)
        report "APPLICATION: Unsupported amount of streams, only 1 is supported for DMA and ETH"
        severity FAILURE;

    -- =========================================================================
    --  CLOCK AND RESETS DEFINED BY USER
    -- =========================================================================

    MI_CLK     <= CLK_USER;
    DMA_CLK    <= CLK_USER;
    DMA_CLK_X2 <= CLK_USER_X4;
    APP_CLK    <= CLK_USER;

    MI_RESET     <= RESET_USER;
    DMA_RESET    <= RESET_USER;
    DMA_RESET_X2 <= RESET_USER_X4;
    APP_RESET    <= RESET_USER;

    -- =========================================================================
    --  MI32 LOGIC
    -- =========================================================================

    mi_async_i : entity work.MI_ASYNC
        generic map(
            ADDR_WIDTH => MI_ADDR_WIDTH,
            DATA_WIDTH => MI_DATA_WIDTH,
            DEVICE     => DEVICE
            )
        port map(
            CLK_M     => MI_CLK,
            RESET_M   => MI_RESET(0),

            MI_M_DWR  => MI_DWR,
            MI_M_ADDR => MI_ADDR,
            MI_M_RD   => MI_RD,
            MI_M_WR   => MI_WR,
            MI_M_BE   => MI_BE,
            MI_M_DRD  => MI_DRD,
            MI_M_ARDY => MI_ARDY,
            MI_M_DRDY => MI_DRDY,

            CLK_S     => APP_CLK,
            RESET_S   => APP_RESET(0),

            MI_S_DWR  => sync_mi_dwr,
            MI_S_ADDR => sync_mi_addr,
            MI_S_RD   => sync_mi_rd,
            MI_S_WR   => sync_mi_wr,
            MI_S_BE   => sync_mi_be,
            MI_S_DRD  => sync_mi_drd,
            MI_S_ARDY => sync_mi_ardy,
            MI_S_DRDY => sync_mi_drdy
            );

    -- =========================================================================
    --  APPLICATION SUBCORE(s)
    -- =========================================================================
    subcore_i : entity work.APP_SUBCORE
        generic map (
            MI_WIDTH => MI_DATA_WIDTH,

            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

            USR_PKT_SIZE_MAX => DMA_RX_FRAME_SIZE_MAX,

            DMA_RX_CHANNELS => DMA_RX_CHANNELS,
            DMA_TX_CHANNELS => DMA_TX_CHANNELS,

            DMA_HDR_META_WIDTH => DMA_HDR_META_WIDTH,
            DEVICE             => DEVICE)
        port map (
            CLK   => APP_CLK,
            RESET => APP_RESET(1),

            DMA_TX_MFB_META_PKT_SIZE => dma_tx_mfb_meta_ins(log2(DMA_TX_FRAME_SIZE_MAX +1) + DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS) -1 downto DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS)),
            DMA_TX_MFB_META_HDR_META => dma_tx_mfb_meta_ins(DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS) -1 downto log2(DMA_TX_CHANNELS)),
            DMA_TX_MFB_META_CHAN     => dma_tx_mfb_meta_ins(log2(DMA_TX_CHANNELS) -1 downto 0),

            DMA_TX_MFB_DATA    => dma_tx_mfb_data_ins,
            DMA_TX_MFB_SOF     => dma_tx_mfb_sof_ins,
            DMA_TX_MFB_EOF     => dma_tx_mfb_eof_ins,
            DMA_TX_MFB_SOF_POS => dma_tx_mfb_sof_pos_ins,
            DMA_TX_MFB_EOF_POS => dma_tx_mfb_eof_pos_ins,
            DMA_TX_MFB_SRC_RDY => dma_tx_mfb_src_rdy_ins,
            DMA_TX_MFB_DST_RDY => dma_tx_mfb_dst_rdy_ins,

            DMA_RX_MFB_META_PKT_SIZE => dma_rx_mfb_meta_pkt_size_ext,
            DMA_RX_MFB_META_HDR_META => dma_rx_mfb_meta_hdr_meta_ext,
            DMA_RX_MFB_META_CHAN     => dma_rx_mfb_meta_chan_ext,

            DMA_RX_MFB_DATA    => dma_rx_mfb_data_ext,
            DMA_RX_MFB_SOF     => dma_rx_mfb_sof_ext,
            DMA_RX_MFB_EOF     => dma_rx_mfb_eof_ext,
            DMA_RX_MFB_SOF_POS => dma_rx_mfb_sof_pos_ext,
            DMA_RX_MFB_EOF_POS => dma_rx_mfb_eof_pos_ext,
            DMA_RX_MFB_SRC_RDY => dma_rx_mfb_src_rdy_ext,
            DMA_RX_MFB_DST_RDY => dma_rx_mfb_dst_rdy_ext,

            MI_DWR  => sync_mi_dwr,
            MI_ADDR => sync_mi_addr,
            MI_BE   => sync_mi_be,
            MI_RD   => sync_mi_rd,
            MI_WR   => sync_mi_wr,
            MI_DRD  => sync_mi_drd,
            MI_ARDY => sync_mi_ardy,
            MI_DRDY => sync_mi_drdy);

    -- =============================================================================================
    -- Extranction and insertion of metadata
    -- =============================================================================================
    dma_tx_dma_meta_insert_i : entity work.METADATA_INSERTOR
        generic map (
            MVB_ITEMS => DMA_STREAMS*MFB_REGIONS,
            MVB_ITEM_WIDTH => log2(DMA_TX_FRAME_SIZE_MAX + 1) + DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS),

            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

            MFB_META_WIDTH => 0,
            INSERT_MODE    => 0,
            MVB_FIFO_SIZE  => 0,
            DEVICE         => DEVICE)
        port map (
            CLK   => APP_CLK,
            RESET => APP_RESET(1),

            RX_MVB_DATA    => DMA_TX_MVB_LEN & DMA_TX_MVB_HDR_META & DMA_TX_MVB_CHANNEL,
            RX_MVB_VLD     => DMA_TX_MVB_VLD,
            RX_MVB_SRC_RDY => DMA_TX_MVB_SRC_RDY(0),
            RX_MVB_DST_RDY => DMA_TX_MVB_DST_RDY(0),

            RX_MFB_DATA    => DMA_TX_MFB_DATA,
            RX_MFB_META    => (others => '0'),
            RX_MFB_SOF     => DMA_TX_MFB_SOF,
            RX_MFB_EOF     => DMA_TX_MFB_EOF,
            RX_MFB_SOF_POS => DMA_TX_MFB_SOF_POS,
            RX_MFB_EOF_POS => DMA_TX_MFB_EOF_POS,
            RX_MFB_SRC_RDY => DMA_TX_MFB_SRC_RDY(0),
            RX_MFB_DST_RDY => DMA_TX_MFB_DST_RDY(0),

            TX_MFB_DATA     => dma_tx_mfb_data_ins,
            TX_MFB_META     => open,
            TX_MFB_META_NEW => dma_tx_mfb_meta_ins,
            TX_MFB_SOF      => dma_tx_mfb_sof_ins,
            TX_MFB_EOF      => dma_tx_mfb_eof_ins,
            TX_MFB_SOF_POS  => dma_tx_mfb_sof_pos_ins,
            TX_MFB_EOF_POS  => dma_tx_mfb_eof_pos_ins,
            TX_MFB_SRC_RDY  => dma_tx_mfb_src_rdy_ins,
            TX_MFB_DST_RDY  => dma_tx_mfb_dst_rdy_ins);

    dma_rx_dma_meta_ext_i : entity work.METADATA_EXTRACTOR
        generic map (
            MVB_ITEMS => DMA_STREAMS*MFB_REGIONS,

            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

            MFB_META_WIDTH  => log2(DMA_RX_FRAME_SIZE_MAX + 1) + DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS),
            EXTRACT_MODE    => 0,
            OUT_MVB_PIPE_EN => FALSE,
            OUT_MFB_PIPE_EN => FALSE,
            DEVICE          => DEVICE)
        port map (
            CLK   => APP_CLK,
            RESET => APP_RESET(1),

            RX_MFB_DATA    => dma_rx_mfb_data_ext,
            RX_MFB_META    => dma_rx_mfb_meta_pkt_size_ext & dma_rx_mfb_meta_hdr_meta_ext & dma_rx_mfb_meta_chan_ext,
            RX_MFB_SOF     => dma_rx_mfb_sof_ext,
            RX_MFB_EOF     => dma_rx_mfb_eof_ext,
            RX_MFB_SOF_POS => dma_rx_mfb_sof_pos_ext,
            RX_MFB_EOF_POS => dma_rx_mfb_eof_pos_ext,
            RX_MFB_SRC_RDY => dma_rx_mfb_src_rdy_ext,
            RX_MFB_DST_RDY => dma_rx_mfb_dst_rdy_ext,

            TX_MVB_DATA    => dma_rx_mvb_data_all,
            TX_MVB_VLD     => DMA_RX_MVB_VLD,
            TX_MVB_SRC_RDY => DMA_RX_MVB_SRC_RDY(0),
            TX_MVB_DST_RDY => DMA_RX_MVB_DST_RDY(0),

            TX_MFB_DATA    => DMA_RX_MFB_DATA,
            TX_MFB_META    => open,
            TX_MFB_SOF     => DMA_RX_MFB_SOF,
            TX_MFB_EOF     => DMA_RX_MFB_EOF,
            TX_MFB_SOF_POS => DMA_RX_MFB_SOF_POS,
            TX_MFB_EOF_POS => DMA_RX_MFB_EOF_POS,
            TX_MFB_SRC_RDY => DMA_RX_MFB_SRC_RDY(0),
            TX_MFB_DST_RDY => DMA_RX_MFB_DST_RDY(0));

    DMA_RX_MVB_LEN      <= dma_rx_mvb_data_all(log2(DMA_RX_FRAME_SIZE_MAX+1) + DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS) -1 downto DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS));
    DMA_RX_MVB_HDR_META <= dma_rx_mvb_data_all(DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS) -1 downto log2(DMA_RX_CHANNELS));
    DMA_RX_MVB_CHANNEL  <= dma_rx_mvb_data_all(log2(DMA_RX_CHANNELS) -1 downto 0);
    DMA_RX_MVB_DISCARD  <= (others => '0');

    -- =============================================================================================
    -- Connection of unused interfaces
    -- =============================================================================================
    ETH_RX_MVB_DST_RDY <= (others => '1');

    eth_loopback_g : if (ETH_STREAMS > 0) generate
        ETH_TX_MFB_DATA    <= ETH_RX_MFB_DATA;
        ETH_TX_MFB_HDR     <= (others => '0');
        ETH_TX_MFB_SOF     <= ETH_RX_MFB_SOF;
        ETH_TX_MFB_EOF     <= ETH_RX_MFB_EOF;
        ETH_TX_MFB_SOF_POS <= ETH_RX_MFB_SOF_POS;
        ETH_TX_MFB_EOF_POS <= ETH_RX_MFB_EOF_POS;
        ETH_TX_MFB_SRC_RDY <= ETH_RX_MFB_SRC_RDY;
        ETH_RX_MFB_DST_RDY <= ETH_TX_MFB_DST_RDY;
    else generate
        ETH_TX_MFB_DATA    <= (others => '0');
        ETH_TX_MFB_HDR     <= (others => '0');
        ETH_TX_MFB_SOF     <= (others => '0');
        ETH_TX_MFB_EOF     <= (others => '0');
        ETH_TX_MFB_SOF_POS <= (others => '0');
        ETH_TX_MFB_EOF_POS <= (others => '0');
        ETH_TX_MFB_SRC_RDY <= (others => '0');
        ETH_RX_MFB_DST_RDY <= (others => '1');
    end generate;

    MEM_AVMM_READ       <= (others => '0');
    MEM_AVMM_WRITE      <= (others => '0');
    MEM_AVMM_ADDRESS    <= (others => (others => '0'));
    MEM_AVMM_BURSTCOUNT <= (others => (others => '0'));
    MEM_AVMM_WRITEDATA  <= (others => (others => '0'));

    MEM_REFR_PERIOD <= (others => (others => '0'));
    MEM_REFR_REQ    <= (others => '0');

    EMIF_RST_REQ        <= (others => '0');
    EMIF_AUTO_PRECHARGE <= (others => '0');
end architecture;
