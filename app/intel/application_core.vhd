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

    -- MI bus signals distribution --
    -- (ETH_STREAMS - 1 downto 0          ) ... eth-signals
    -- (MEM_PORTS   - 1 downto ETH_STREAMS) ... mem-signals
    constant MI_PORTS_RAW      : natural := ETH_STREAMS + MEM_PORTS;
    constant MI_PORTS          : natural := 2 ** log2(MI_PORTS_RAW);
    constant DMA_RX_ALL_META_W : natural := log2(DMA_PKT_MTU+1) + DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS) + 1;
    constant DMA_TX_ALL_META_W : natural := log2(DMA_PKT_MTU+1) + DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS);

    function mi_addr_base_f return slv_array_t is
        constant ADDR_W    : natural := 25;
        constant SUBADDR_W : natural := ADDR_W-log2(MI_PORTS);
        variable v_addr_base : slv_array_t(MI_PORTS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0) := (others => (others => '0'));
    begin
        for i in 0 to MI_PORTS-1 loop
            v_addr_base(i) := std_logic_vector(to_unsigned(i*2**SUBADDR_W,MI_ADDR_WIDTH));
        end loop;
        return v_addr_base;
    end function;

    -- ============================================== MVB ==============================================
    signal eth_rx_mvb_data_deser         : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal eth_rx_mvb_vld_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal app_dma_rx_mvb_len_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
    signal app_dma_rx_mvb_hdr_meta_deser : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal app_dma_rx_mvb_channel_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal app_dma_rx_mvb_discard_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_data_deser     : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_RX_ALL_META_W-1 downto 0);
    signal app_dma_rx_mvb_vld_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_rx_mvb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal app_dma_tx_mvb_len_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
    signal app_dma_tx_mvb_hdr_meta_deser : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal app_dma_tx_mvb_channel_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    signal app_dma_tx_mvb_data_deser     : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_TX_ALL_META_W-1 downto 0);
    signal app_dma_tx_mvb_vld_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mvb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_tx_mvb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal dma_rx_mvb_len_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
    signal dma_rx_mvb_hdr_meta_deser     : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal dma_rx_mvb_channel_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal dma_rx_mvb_discard_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mvb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_RX_ALL_META_W-1 downto 0);
    signal dma_rx_mvb_vld_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mvb_src_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_rx_mvb_dst_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal dma_tx_mvb_len_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_PKT_MTU+1)-1 downto 0);
    signal dma_tx_mvb_hdr_meta_deser     : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal dma_tx_mvb_channel_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    signal dma_tx_mvb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_TX_ALL_META_W-1 downto 0);
    signal dma_tx_mvb_switch_deser       : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(ETH_STREAMS)-1 downto 0);
    signal dma_tx_mvb_vld_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_tx_mvb_src_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_tx_mvb_dst_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- ============================================== MFB ==============================================
    signal eth_rx_mfb_data_deser         : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal eth_rx_mfb_sof_pos_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal eth_rx_mfb_eof_pos_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal eth_rx_mfb_sof_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal eth_rx_mfb_eof_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal eth_tx_mfb_data_deser         : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal eth_tx_mfb_hdr_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0);
    signal eth_tx_mfb_sof_pos_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal eth_tx_mfb_eof_pos_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal eth_tx_mfb_sof_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal eth_tx_mfb_eof_deser          : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

    signal app_dma_rx_mfb_data_deser     : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal app_dma_rx_mfb_sof_pos_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal app_dma_rx_mfb_eof_pos_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal app_dma_rx_mfb_sof_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mfb_eof_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mfb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_rx_mfb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal app_dma_tx_mfb_data_deser     : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal app_dma_tx_mfb_sof_pos_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal app_dma_tx_mfb_eof_pos_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal app_dma_tx_mfb_sof_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mfb_eof_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mfb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_tx_mfb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal dma_rx_mfb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dma_rx_mfb_sof_pos_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal dma_rx_mfb_eof_pos_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_rx_mfb_sof_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mfb_eof_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mfb_src_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_rx_mfb_dst_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal dma_tx_mfb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dma_tx_mfb_sof_pos_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal dma_tx_mfb_eof_pos_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_tx_mfb_sof_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_tx_mfb_eof_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_tx_mfb_src_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_tx_mfb_dst_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- ============================================== MI ==============================================
    signal sync_mi_dwr                   : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_addr                  : std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    signal sync_mi_be                    : std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    signal sync_mi_rd                    : std_logic;
    signal sync_mi_wr                    : std_logic;
    signal sync_mi_drd                   : std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    signal sync_mi_ardy                  : std_logic;
    signal sync_mi_drdy                  : std_logic;

    signal split_mi_dwr                  : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal split_mi_addr                 : slv_array_t     (MI_PORTS-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal split_mi_be                   : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal split_mi_rd                   : std_logic_vector(MI_PORTS-1 downto 0);
    signal split_mi_wr                   : std_logic_vector(MI_PORTS-1 downto 0);
    signal split_mi_ardy                 : std_logic_vector(MI_PORTS-1 downto 0) := (others => '0');
    signal split_mi_drd                  : slv_array_t     (MI_PORTS-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal split_mi_drdy                 : std_logic_vector(MI_PORTS-1 downto 0) := (others => '0');

begin

    assert ((DMA_STREAMS = ETH_STREAMS) or (DMA_STREAMS < ETH_STREAMS and DMA_STREAMS = 1))
        report "The number of DMA_STREAMS must be equal to ETH_STREAMS, or DMA_STREAMS must be 1 and DMA_STREAMS < ETH_STREAMS!"
        severity failure;

    -- =========================================================================
    --  CLOCK AND RESETS DEFINED BY USER
    -- =========================================================================

    MI_CLK     <= CLK_USER;
    DMA_CLK    <= CLK_USER_X2;
    DMA_CLK_X2 <= CLK_USER_X4;
    APP_CLK    <= CLK_USER_X2;

    MI_RESET     <= RESET_USER;
    DMA_RESET    <= RESET_USER_X2;
    DMA_RESET_X2 <= RESET_USER_X4;
    APP_RESET    <= RESET_USER_X2;

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
        -- Master interface
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

        -- Slave interface
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

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        PORTS      => MI_PORTS,
        ADDR_BASE  => mi_addr_base_f,
        DEVICE     => DEVICE
    )
    port map(
        CLK        => APP_CLK,
        RESET      => APP_RESET(0),
        
        RX_DWR     => sync_mi_dwr,
        RX_ADDR    => sync_mi_addr,
        RX_BE      => sync_mi_be,
        RX_RD      => sync_mi_rd,
        RX_WR      => sync_mi_wr,
        RX_ARDY    => sync_mi_ardy,
        RX_DRD     => sync_mi_drd,
        RX_DRDY    => sync_mi_drdy,

        TX_DWR     => split_mi_dwr,
        TX_ADDR    => split_mi_addr,
        TX_BE      => split_mi_be,
        TX_RD      => split_mi_rd,
        TX_WR      => split_mi_wr,
        TX_ARDY    => split_mi_ardy,
        TX_DRD     => split_mi_drd,
        TX_DRDY    => split_mi_drdy
    );

    -- =========================================================================
    --  APPLICATION STREAMS
    -- =========================================================================

    eth_rx_mvb_data_deser <= slv_array_deser(ETH_RX_MVB_DATA,ETH_STREAMS);
    eth_rx_mvb_vld_deser  <= slv_array_deser(ETH_RX_MVB_VLD,ETH_STREAMS);

    eth_rx_mfb_data_deser    <= slv_array_deser(ETH_RX_MFB_DATA,ETH_STREAMS);
    eth_rx_mfb_sof_pos_deser <= slv_array_deser(ETH_RX_MFB_SOF_POS,ETH_STREAMS);
    eth_rx_mfb_eof_pos_deser <= slv_array_deser(ETH_RX_MFB_EOF_POS,ETH_STREAMS);
    eth_rx_mfb_sof_deser     <= slv_array_deser(ETH_RX_MFB_SOF,ETH_STREAMS);
    eth_rx_mfb_eof_deser     <= slv_array_deser(ETH_RX_MFB_EOF,ETH_STREAMS);

    ETH_TX_MFB_DATA    <= slv_array_ser(eth_tx_mfb_data_deser);
    ETH_TX_MFB_HDR     <= slv_array_ser(eth_tx_mfb_hdr_deser);
    ETH_TX_MFB_SOF_POS <= slv_array_ser(eth_tx_mfb_sof_pos_deser);
    ETH_TX_MFB_EOF_POS <= slv_array_ser(eth_tx_mfb_eof_pos_deser);
    ETH_TX_MFB_SOF     <= slv_array_ser(eth_tx_mfb_sof_deser);
    ETH_TX_MFB_EOF     <= slv_array_ser(eth_tx_mfb_eof_deser);

    subcore_g : for i in ETH_STREAMS-1 downto 0 generate
        subcore_i : entity work.APP_SUBCORE
        generic map(
            MFB_REGIONS        => MFB_REGIONS,
            MFB_REG_SIZE       => MFB_REG_SIZE,
            MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,
            MI_ADDR_WIDTH      => MI_ADDR_WIDTH,
            MI_DATA_WIDTH      => MI_DATA_WIDTH,
            SUBCORE_ID         => i,
            ETH_CHANNELS       => ETH_CHANNELS,
            USR_PKT_SIZE_MAX   => DMA_PKT_MTU,
            DMA_RX_CHANNELS    => DMA_RX_CHANNELS,
            DMA_TX_CHANNELS    => DMA_TX_CHANNELS,
            DMA_HDR_META_WIDTH => DMA_HDR_META_WIDTH,
            DEVICE             => DEVICE
        )
        port map(
            CLK                     => APP_CLK,
            RESET                   => APP_RESET(1),

            DMA_RX_MVB_LEN          => app_dma_rx_mvb_len_deser(i),
            DMA_RX_MVB_HDR_META     => app_dma_rx_mvb_hdr_meta_deser(i),
            DMA_RX_MVB_CHANNEL      => app_dma_rx_mvb_channel_deser(i),
            DMA_RX_MVB_DISCARD      => app_dma_rx_mvb_discard_deser(i),
            DMA_RX_MVB_VLD          => app_dma_rx_mvb_vld_deser(i),
            DMA_RX_MVB_SRC_RDY      => app_dma_rx_mvb_src_rdy_deser(i),
            DMA_RX_MVB_DST_RDY      => app_dma_rx_mvb_dst_rdy_deser(i),

            DMA_RX_MFB_DATA         => app_dma_rx_mfb_data_deser(i),
            DMA_RX_MFB_SOF          => app_dma_rx_mfb_sof_deser(i),
            DMA_RX_MFB_EOF          => app_dma_rx_mfb_eof_deser(i),
            DMA_RX_MFB_SOF_POS      => app_dma_rx_mfb_sof_pos_deser(i),
            DMA_RX_MFB_EOF_POS      => app_dma_rx_mfb_eof_pos_deser(i),
            DMA_RX_MFB_SRC_RDY      => app_dma_rx_mfb_src_rdy_deser(i),
            DMA_RX_MFB_DST_RDY      => app_dma_rx_mfb_dst_rdy_deser(i),

            DMA_TX_MVB_LEN          => app_dma_tx_mvb_len_deser(i),
            DMA_TX_MVB_HDR_META     => app_dma_tx_mvb_hdr_meta_deser(i),
            DMA_TX_MVB_CHANNEL      => app_dma_tx_mvb_channel_deser(i),
            DMA_TX_MVB_VLD          => app_dma_tx_mvb_vld_deser(i),
            DMA_TX_MVB_SRC_RDY      => app_dma_tx_mvb_src_rdy_deser(i),
            DMA_TX_MVB_DST_RDY      => app_dma_tx_mvb_dst_rdy_deser(i),

            DMA_TX_MFB_DATA         => app_dma_tx_mfb_data_deser(i),
            DMA_TX_MFB_SOF          => app_dma_tx_mfb_sof_deser(i),
            DMA_TX_MFB_EOF          => app_dma_tx_mfb_eof_deser(i),
            DMA_TX_MFB_SOF_POS      => app_dma_tx_mfb_sof_pos_deser(i),
            DMA_TX_MFB_EOF_POS      => app_dma_tx_mfb_eof_pos_deser(i),
            DMA_TX_MFB_SRC_RDY      => app_dma_tx_mfb_src_rdy_deser(i),
            DMA_TX_MFB_DST_RDY      => app_dma_tx_mfb_dst_rdy_deser(i),
        
            ETH_RX_MVB_DATA         => eth_rx_mvb_data_deser(i),
            ETH_RX_MVB_VLD          => eth_rx_mvb_vld_deser(i),
            ETH_RX_MVB_SRC_RDY      => ETH_RX_MVB_SRC_RDY(i),
            ETH_RX_MVB_DST_RDY      => ETH_RX_MVB_DST_RDY(i),

            ETH_RX_MFB_DATA         => eth_rx_mfb_data_deser(i),
            ETH_RX_MFB_SOF          => eth_rx_mfb_sof_deser(i),
            ETH_RX_MFB_EOF          => eth_rx_mfb_eof_deser(i),
            ETH_RX_MFB_SOF_POS      => eth_rx_mfb_sof_pos_deser(i),
            ETH_RX_MFB_EOF_POS      => eth_rx_mfb_eof_pos_deser(i),
            ETH_RX_MFB_SRC_RDY      => ETH_RX_MFB_SRC_RDY(i),
            ETH_RX_MFB_DST_RDY      => ETH_RX_MFB_DST_RDY(i),
        
            ETH_TX_MFB_DATA         => eth_tx_mfb_data_deser(i),
            ETH_TX_MFB_HDR          => eth_tx_mfb_hdr_deser(i),
            ETH_TX_MFB_SOF          => eth_tx_mfb_sof_deser(i),
            ETH_TX_MFB_EOF          => eth_tx_mfb_eof_deser(i),
            ETH_TX_MFB_SOF_POS      => eth_tx_mfb_sof_pos_deser(i),
            ETH_TX_MFB_EOF_POS      => eth_tx_mfb_eof_pos_deser(i),
            ETH_TX_MFB_SRC_RDY      => ETH_TX_MFB_SRC_RDY(i),
            ETH_TX_MFB_DST_RDY      => ETH_TX_MFB_DST_RDY(i),
            
            MI_DWR                  => split_mi_dwr(i),
            MI_ADDR                 => split_mi_addr(i),
            MI_BE                   => split_mi_be(i),
            MI_RD                   => split_mi_rd(i),
            MI_WR                   => split_mi_wr(i),
            MI_DRD                  => split_mi_drd(i),
            MI_ARDY                 => split_mi_ardy(i),
            MI_DRDY                 => split_mi_drdy(i)
        );
    end generate;

    -- =========================================================================
    --  DMA MODULE(S) CONNECTION
    -- =========================================================================

    -- simple connection
    dma2app_eq_g: if (DMA_STREAMS = ETH_STREAMS) generate
        dma_rx_mvb_len_deser          <= app_dma_rx_mvb_len_deser;
        dma_rx_mvb_hdr_meta_deser     <= app_dma_rx_mvb_hdr_meta_deser;
        dma_rx_mvb_channel_deser      <= app_dma_rx_mvb_channel_deser;
        dma_rx_mvb_discard_deser      <= app_dma_rx_mvb_discard_deser;
        dma_rx_mvb_vld_deser          <= app_dma_rx_mvb_vld_deser;
        dma_rx_mvb_src_rdy_deser      <= app_dma_rx_mvb_src_rdy_deser;
        app_dma_rx_mvb_dst_rdy_deser  <= dma_rx_mvb_dst_rdy_deser;

        dma_rx_mfb_data_deser         <= app_dma_rx_mfb_data_deser;
        dma_rx_mfb_sof_pos_deser      <= app_dma_rx_mfb_sof_pos_deser;
        dma_rx_mfb_eof_pos_deser      <= app_dma_rx_mfb_eof_pos_deser;
        dma_rx_mfb_sof_deser          <= app_dma_rx_mfb_sof_deser;
        dma_rx_mfb_eof_deser          <= app_dma_rx_mfb_eof_deser;
        dma_rx_mfb_src_rdy_deser      <= app_dma_rx_mfb_src_rdy_deser;
        app_dma_rx_mfb_dst_rdy_deser  <= dma_rx_mfb_dst_rdy_deser;

        app_dma_tx_mvb_len_deser      <= dma_tx_mvb_len_deser;
        app_dma_tx_mvb_hdr_meta_deser <= dma_tx_mvb_hdr_meta_deser;
        app_dma_tx_mvb_channel_deser  <= dma_tx_mvb_channel_deser;
        app_dma_tx_mvb_vld_deser      <= dma_tx_mvb_vld_deser;
        app_dma_tx_mvb_src_rdy_deser  <= dma_tx_mvb_src_rdy_deser;
        dma_tx_mvb_dst_rdy_deser      <= app_dma_tx_mvb_dst_rdy_deser;
    
        app_dma_tx_mfb_data_deser     <= dma_tx_mfb_data_deser;
        app_dma_tx_mfb_sof_pos_deser  <= dma_tx_mfb_sof_pos_deser;
        app_dma_tx_mfb_eof_pos_deser  <= dma_tx_mfb_eof_pos_deser;
        app_dma_tx_mfb_sof_deser      <= dma_tx_mfb_sof_deser;
        app_dma_tx_mfb_eof_deser      <= dma_tx_mfb_eof_deser;
        app_dma_tx_mfb_src_rdy_deser  <= dma_tx_mfb_src_rdy_deser;
        dma_tx_mfb_dst_rdy_deser      <= app_dma_tx_mfb_dst_rdy_deser;
    end generate;

    -- merge each ETH stream to single DMA stream
    dma2app_one_g: if (DMA_STREAMS < ETH_STREAMS and DMA_STREAMS = 1) generate
        dma_rx_mvb_data_g: for i in 0 to DMA_STREAMS-1 generate
            dma_rx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W)                                                                                                 <= app_dma_rx_mvb_discard_deser(i)(r);
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W+1)                                          <= app_dma_rx_mvb_channel_deser(i)((r+1)*log2(DMA_RX_CHANNELS)-1 downto r*log2(DMA_RX_CHANNELS));
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)) <= app_dma_rx_mvb_hdr_meta_deser(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH);
                app_dma_rx_mvb_data_deser(i)((r+1)*DMA_RX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH)                     <= app_dma_rx_mvb_len_deser(i)((r+1)*log2(DMA_PKT_MTU+1)-1 downto r*log2(DMA_PKT_MTU+1));

                dma_rx_mvb_discard_deser(i)(r)                                                            <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W);
                dma_rx_mvb_channel_deser(i)((r+1)*log2(DMA_RX_CHANNELS)-1 downto r*log2(DMA_RX_CHANNELS)) <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W+1);
                dma_rx_mvb_hdr_meta_deser(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH)      <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS));
                dma_rx_mvb_len_deser(i)((r+1)*log2(DMA_PKT_MTU+1)-1 downto r*log2(DMA_PKT_MTU+1))         <= dma_rx_mvb_data_deser(i)((r+1)*DMA_RX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH);
            end generate;
        end generate;

        mfb_merger_tree_i : entity work.MFB_MERGER_GEN
        generic map(
            MERGER_INPUTS   => ETH_STREAMS,
            MVB_ITEMS       => MFB_REGIONS,
            MVB_ITEM_WIDTH  => DMA_RX_ALL_META_W,
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REG_SIZE    => MFB_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            INPUT_FIFO_SIZE => 8,
            RX_PAYLOAD_EN   => (others => true),
            IN_PIPE_EN      => false,
            OUT_PIPE_EN     => true,
            DEVICE          => DEVICE
        )
        port map(
            CLK             => APP_CLK,
            RESET           => APP_RESET(2),
                
            RX_MVB_DATA     => app_dma_rx_mvb_data_deser,
            RX_MVB_PAYLOAD  => (others => (others => '1')),
            RX_MVB_VLD      => app_dma_rx_mvb_vld_deser,
            RX_MVB_SRC_RDY  => app_dma_rx_mvb_src_rdy_deser,
            RX_MVB_DST_RDY  => app_dma_rx_mvb_dst_rdy_deser,
    
            RX_MFB_DATA     => app_dma_rx_mfb_data_deser,
            RX_MFB_SOF      => app_dma_rx_mfb_sof_deser,
            RX_MFB_EOF      => app_dma_rx_mfb_eof_deser,
            RX_MFB_SOF_POS  => app_dma_rx_mfb_sof_pos_deser,
            RX_MFB_EOF_POS  => app_dma_rx_mfb_eof_pos_deser,
            RX_MFB_SRC_RDY  => app_dma_rx_mfb_src_rdy_deser,
            RX_MFB_DST_RDY  => app_dma_rx_mfb_dst_rdy_deser,

            TX_MVB_DATA     => dma_rx_mvb_data_deser(0),
            TX_MVB_VLD      => dma_rx_mvb_vld_deser(0),
            TX_MVB_SRC_RDY  => dma_rx_mvb_src_rdy_deser(0),
            TX_MVB_DST_RDY  => dma_rx_mvb_dst_rdy_deser(0),
    
            TX_MFB_DATA     => dma_rx_mfb_data_deser(0),
            TX_MFB_SOF      => dma_rx_mfb_sof_deser(0),
            TX_MFB_EOF      => dma_rx_mfb_eof_deser(0),
            TX_MFB_SOF_POS  => dma_rx_mfb_sof_pos_deser(0),
            TX_MFB_EOF_POS  => dma_rx_mfb_eof_pos_deser(0),
            TX_MFB_SRC_RDY  => dma_rx_mfb_src_rdy_deser(0),
            TX_MFB_DST_RDY  => dma_rx_mfb_dst_rdy_deser(0)
        );

        dma_tx_mvb_data_g: for i in 0 to DMA_STREAMS-1 generate
            dma_tx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W)                                          <= dma_tx_mvb_channel_deser(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto r*log2(DMA_TX_CHANNELS));
                dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+log2(DMA_TX_CHANNELS)) <= dma_tx_mvb_hdr_meta_deser(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH);
                dma_tx_mvb_data_deser(i)((r+1)*DMA_TX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH)                   <= dma_tx_mvb_len_deser(i)((r+1)*log2(DMA_PKT_MTU+1)-1 downto r*log2(DMA_PKT_MTU+1));

                dma_tx_mvb_switch_deser(i)((r+1)*log2(ETH_STREAMS)-1 downto r*log2(ETH_STREAMS)) <= dma_tx_mvb_channel_deser(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto (r+1)*log2(DMA_TX_CHANNELS)-log2(ETH_STREAMS));

                app_dma_tx_mvb_channel_deser(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto r*log2(DMA_TX_CHANNELS)) <= app_dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W);
                app_dma_tx_mvb_hdr_meta_deser(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH)      <= app_dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+log2(DMA_TX_CHANNELS));
                app_dma_tx_mvb_len_deser(i)((r+1)*log2(DMA_PKT_MTU+1)-1 downto r*log2(DMA_PKT_MTU+1))         <= app_dma_tx_mvb_data_deser(i)((r+1)*DMA_TX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH);
            end generate;
        end generate;

        mfb_splitter_tree_i : entity work.MFB_SPLITTER_GEN
        generic map(
            SPLITTER_OUTPUTS => ETH_STREAMS,
            MVB_ITEMS        => MFB_REGIONS,
            MVB_ITEM_WIDTH   => DMA_TX_ALL_META_W,
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REG_SIZE     => MFB_REG_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
            OUTPUT_FIFO_SIZE => 8,
            OUT_PIPE_EN      => true,
            DEVICE           => DEVICE
        )
        port map(
            CLK             => APP_CLK,
            RESET           => APP_RESET(2),

            RX_MVB_DATA     => dma_tx_mvb_data_deser(0),
            RX_MVB_SWITCH   => dma_tx_mvb_switch_deser(0),
            RX_MVB_PAYLOAD  => (others => '1'),
            RX_MVB_VLD      => dma_tx_mvb_vld_deser(0),
            RX_MVB_SRC_RDY  => dma_tx_mvb_src_rdy_deser(0),
            RX_MVB_DST_RDY  => dma_tx_mvb_dst_rdy_deser(0),
    
            RX_MFB_DATA     => dma_tx_mfb_data_deser(0),
            RX_MFB_SOF      => dma_tx_mfb_sof_deser(0),
            RX_MFB_EOF      => dma_tx_mfb_eof_deser(0),
            RX_MFB_SOF_POS  => dma_tx_mfb_sof_pos_deser(0),
            RX_MFB_EOF_POS  => dma_tx_mfb_eof_pos_deser(0),
            RX_MFB_SRC_RDY  => dma_tx_mfb_src_rdy_deser(0),
            RX_MFB_DST_RDY  => dma_tx_mfb_dst_rdy_deser(0),

            TX_MVB_DATA     => app_dma_tx_mvb_data_deser,
            TX_MVB_VLD      => app_dma_tx_mvb_vld_deser,
            TX_MVB_SRC_RDY  => app_dma_tx_mvb_src_rdy_deser,
            TX_MVB_DST_RDY  => app_dma_tx_mvb_dst_rdy_deser,
    
            TX_MFB_DATA     => app_dma_tx_mfb_data_deser,
            TX_MFB_SOF      => app_dma_tx_mfb_sof_deser,
            TX_MFB_EOF      => app_dma_tx_mfb_eof_deser,
            TX_MFB_SOF_POS  => app_dma_tx_mfb_sof_pos_deser,
            TX_MFB_EOF_POS  => app_dma_tx_mfb_eof_pos_deser,
            TX_MFB_SRC_RDY  => app_dma_tx_mfb_src_rdy_deser,
            TX_MFB_DST_RDY  => app_dma_tx_mfb_dst_rdy_deser
        );
    end generate;

    DMA_RX_MVB_LEN           <= slv_array_ser(dma_rx_mvb_len_deser);
    DMA_RX_MVB_HDR_META      <= slv_array_ser(dma_rx_mvb_hdr_meta_deser);
    DMA_RX_MVB_CHANNEL       <= slv_array_ser(dma_rx_mvb_channel_deser);
    DMA_RX_MVB_DISCARD       <= slv_array_ser(dma_rx_mvb_discard_deser);
    DMA_RX_MVB_VLD           <= slv_array_ser(dma_rx_mvb_vld_deser);
    DMA_RX_MVB_SRC_RDY       <= dma_rx_mvb_src_rdy_deser;
    dma_rx_mvb_dst_rdy_deser <= DMA_RX_MVB_DST_RDY;

    DMA_RX_MFB_DATA          <= slv_array_ser(dma_rx_mfb_data_deser);
    DMA_RX_MFB_SOF_POS       <= slv_array_ser(dma_rx_mfb_sof_pos_deser);
    DMA_RX_MFB_EOF_POS       <= slv_array_ser(dma_rx_mfb_eof_pos_deser);
    DMA_RX_MFB_SOF           <= slv_array_ser(dma_rx_mfb_sof_deser);
    DMA_RX_MFB_EOF           <= slv_array_ser(dma_rx_mfb_eof_deser);
    DMA_RX_MFB_SRC_RDY       <= dma_rx_mfb_src_rdy_deser;
    dma_rx_mfb_dst_rdy_deser <= DMA_RX_MFB_DST_RDY;

    dma_tx_mvb_len_deser      <= slv_array_deser(DMA_TX_MVB_LEN,DMA_STREAMS);
    dma_tx_mvb_hdr_meta_deser <= slv_array_deser(DMA_TX_MVB_HDR_META,DMA_STREAMS);
    dma_tx_mvb_channel_deser  <= slv_array_deser(DMA_TX_MVB_CHANNEL,DMA_STREAMS);
    dma_tx_mvb_vld_deser      <= slv_array_deser(DMA_TX_MVB_VLD,DMA_STREAMS);
    dma_tx_mvb_src_rdy_deser  <= DMA_TX_MVB_SRC_RDY;
    DMA_TX_MVB_DST_RDY        <= dma_tx_mvb_dst_rdy_deser;

    dma_tx_mfb_data_deser    <= slv_array_deser(DMA_TX_MFB_DATA,DMA_STREAMS);
    dma_tx_mfb_sof_pos_deser <= slv_array_deser(DMA_TX_MFB_SOF_POS,DMA_STREAMS);
    dma_tx_mfb_eof_pos_deser <= slv_array_deser(DMA_TX_MFB_EOF_POS,DMA_STREAMS);
    dma_tx_mfb_sof_deser     <= slv_array_deser(DMA_TX_MFB_SOF,DMA_STREAMS);
    dma_tx_mfb_eof_deser     <= slv_array_deser(DMA_TX_MFB_EOF,DMA_STREAMS);
    dma_tx_mfb_src_rdy_deser <= DMA_TX_MFB_SRC_RDY;
    DMA_TX_MFB_DST_RDY       <= dma_tx_mfb_dst_rdy_deser;

    -- =========================================================================
    --  MEMORY TESTERS
    -- =========================================================================

    mem_testers_g : for i in MEM_PORTS -1 downto 0 generate
        mem_tester_i : entity work.MEM_TESTER
        generic map (
            AMM_DATA_WIDTH              => MEM_DATA_WIDTH,
            AMM_ADDR_WIDTH              => MEM_ADDR_WIDTH,
            AMM_BURST_COUNT_WIDTH       => MEM_BURST_WIDTH,
            AMM_FREQ_KHZ                => AMM_FREQ_KHZ,

            MI_DATA_WIDTH               => MI_DATA_WIDTH,
            MI_ADDR_WIDTH               => MI_ADDR_WIDTH,
     
            RAND_GEN_DATA_WIDTH         => 64,
            RAND_GEN_ADDR_WIDTH         => 32,
            RANDOM_DATA_SEED            => 
                (
                    X"04a90474c868e517",
                    X"8b9d55e316e57bfc",
                    X"0554f750a3702377",
                    X"abcd76981c982117",
                    X"fc21f22c3ad6d735",
                    X"5d06b6ae01cf86f8",
                    X"38fc9671a56bb8e8",
                    X"457a2fb6bd25f1fa"
                ),
            RANDOM_ADDR_SEED            => X"FEFE01FF",
            DEVICE                      => DEVICE
        )
        port map(
            AMM_CLK                     => MEM_CLK                  (i),
            AMM_RST                     => MEM_RST                  (i),
     
            AMM_READY                   => MEM_AVMM_READY           (i),
            AMM_READ                    => MEM_AVMM_READ            (i),
            AMM_WRITE                   => MEM_AVMM_WRITE           (i),
            AMM_ADDRESS                 => MEM_AVMM_ADDRESS         (i),
            AMM_READ_DATA               => MEM_AVMM_READDATA        (i),
            AMM_WRITE_DATA              => MEM_AVMM_WRITEDATA       (i),
            AMM_BURST_COUNT             => MEM_AVMM_BURSTCOUNT      (i),
            AMM_READ_DATA_VALID         => MEM_AVMM_READDATAVALID   (i),
     
            EMIF_RST_REQ                => EMIF_RST_REQ             (i),
            EMIF_RST_DONE               => EMIF_RST_DONE            (i),
            EMIF_ECC_ISR                => EMIF_ECC_USR_INT         (i),
            EMIF_CAL_SUCCESS            => EMIF_CAL_SUCCESS         (i),
            EMIF_CAL_FAIL               => EMIF_CAL_FAIL            (i),
     
            MI_CLK                      => APP_CLK, 
            MI_RST                      => APP_RESET                (0), -- TODO
            MI_DWR                      => split_mi_dwr             (i + ETH_STREAMS),
            MI_ADDR                     => split_mi_addr            (i + ETH_STREAMS),
            MI_BE                       => split_mi_be              (i + ETH_STREAMS),
            MI_RD                       => split_mi_rd              (i + ETH_STREAMS),
            MI_WR                       => split_mi_wr              (i + ETH_STREAMS),
            MI_ARDY                     => split_mi_ardy            (i + ETH_STREAMS),
            MI_DRD                      => split_mi_drd             (i + ETH_STREAMS),
            MI_DRDY                     => split_mi_drdy            (i + ETH_STREAMS)
        );
    end generate;

end architecture;
