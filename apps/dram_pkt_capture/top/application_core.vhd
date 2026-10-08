-- application_core.vhd: User application core
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Daniel Kondys  <xkondy00@vutbr.cz>
--            Adam Zatloukal <zatloukal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;
use work.ndk_fpga_top_pkg.all;
use work.ndk_fpga_common_pkg.all;

architecture FULL of APPLICATION_CORE is

    constant APP_ST_PER_DMA_ST : natural := ETH_STREAMS/DMA_STREAMS;
    constant CORE_DMA_RX_CHAN  : natural := DMA_RX_CHANNELS/APP_ST_PER_DMA_ST;
    constant CORE_DMA_TX_CHAN  : natural := DMA_TX_CHANNELS/APP_ST_PER_DMA_ST;

    -- MI bus signals distribution --
    -- (ETH_STREAMS - 1 downto 0) ==> eth-signals
    constant MI_PORTS          : natural := ETH_STREAMS;

    type     mem_target_t is (MEM_TGT_BRAM, MEM_TGT_EXT_DDR);
    constant MEM_TARGET : mem_target_t := MEM_TGT_EXT_DDR;

    -- Depth of the on-chip memory model used when MEM_TARGET = MEM_TGT_BRAM.
    constant BRAM_ADDR_WIDTH : natural := 13;

    constant RING_ADDR_WIDTH : natural :=
        tsel(MEM_TARGET = MEM_TGT_BRAM, BRAM_ADDR_WIDTH, MEM_ADDR_WIDTH);


    function mi_addr_base_f return slv_array_t is
        constant ADDR_W      : natural := 25;
        constant SUBADDR_W   : natural := ADDR_W-log2(MI_PORTS);
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

    signal app_dma_rx_mvb_len_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal app_dma_rx_mvb_hdr_meta_deser : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal app_dma_rx_mvb_channel_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal app_dma_rx_mvb_channel_mod    : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(CORE_DMA_RX_CHAN)-1 downto 0);
    signal app_dma_rx_mvb_discard_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_vld_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_rx_mvb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_rx_mvb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal app_dma_tx_mvb_len_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal app_dma_tx_mvb_hdr_meta_deser : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal app_dma_tx_mvb_channel_deser  : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    signal app_dma_tx_mvb_channel_mod    : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS*log2(CORE_DMA_TX_CHAN)-1 downto 0);
    signal app_dma_tx_mvb_vld_deser      : slv_array_t(ETH_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mvb_src_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);
    signal app_dma_tx_mvb_dst_rdy_deser  : std_logic_vector(ETH_STREAMS-1 downto 0);

    signal dma_rx_mvb_len_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal dma_rx_mvb_hdr_meta_deser     : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal dma_rx_mvb_channel_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal dma_rx_mvb_discard_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mvb_vld_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_rx_mvb_src_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal dma_rx_mvb_dst_rdy_deser      : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal dma_tx_mvb_len_deser          : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    signal dma_tx_mvb_hdr_meta_deser     : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    signal dma_tx_mvb_channel_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
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

    signal int_avmm_address       : slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal int_avmm_burstcount    : slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal int_avmm_write         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal int_avmm_writedata     : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal int_avmm_read          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal int_avmm_ready         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal int_avmm_readdata      : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal int_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0);

begin

    assert ((DMA_STREAMS = ETH_STREAMS) or (DMA_STREAMS < ETH_STREAMS and DMA_STREAMS = 1))
        report "APPLICATION: The number of DMA_STREAMS must be equal to ETH_STREAMS, or DMA_STREAMS must be 1 and DMA_STREAMS < ETH_STREAMS!"
        severity failure;


    assert (MEM_PORTS = 2*ETH_STREAMS)
        report "APPLICATION: DRAM packet capture needs two memory ports per ETH stream (n6010, 100g2)."
        severity failure;

    assert (MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH = 2*MEM_DATA_WIDTH)
        report "APPLICATION: The MFB word must be as wide as two memory ports."
        severity failure;

    mtu_assert_g: for p in 0 to ETH_PORTS-1 generate
        assert ((DMA_RX_FRAME_SIZE_MAX = ETH_PORT_RX_MTU(p)) and (DMA_TX_FRAME_SIZE_MAX = ETH_PORT_TX_MTU(p)) and (DMA_RX_FRAME_SIZE_MAX = DMA_TX_FRAME_SIZE_MAX))
            report "APPLICATION: The maximum frame size for RX/TX DMA and RX/TX ETH must be the same or the user must implement the conversion of frames with incompatible sizes in their own application logic!"
            severity failure;
    end generate;

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
    generic map (
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        DEVICE     => DEVICE
    )
    port map (
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
    generic map (
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        PORTS      => MI_PORTS,
        ADDR_BASE  => mi_addr_base_f,
        DEVICE     => DEVICE
    )
    port map (
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
    --  APPLICATION CORES
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

    core_g : for i in ETH_STREAMS-1 downto 0 generate
        core_i : entity work.APP_SUBCORE
        generic map (
            MFB_REGIONS        => MFB_REGIONS,
            MFB_REG_SIZE       => MFB_REG_SIZE,
            MFB_BLOCK_SIZE     => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH     => MFB_ITEM_WIDTH,
            MI_ADDR_WIDTH      => MI_ADDR_WIDTH,
            MI_DATA_WIDTH      => MI_DATA_WIDTH,
            MEM_ADDR_WIDTH     => MEM_ADDR_WIDTH,
            RING_ADDR_WIDTH    => RING_ADDR_WIDTH,
            MEM_BURST_WIDTH    => MEM_BURST_WIDTH,
            MEM_DATA_WIDTH     => MEM_DATA_WIDTH,
            SUBCORE_ID         => i,
            ETH_CHANNELS       => ETH_CHANNELS,
            USR_PKT_SIZE_MAX   => DMA_RX_FRAME_SIZE_MAX,
            DMA_RX_CHANNELS    => CORE_DMA_RX_CHAN,
            DMA_TX_CHANNELS    => CORE_DMA_TX_CHAN,
            DMA_HDR_META_WIDTH => DMA_HDR_META_WIDTH,
            DEVICE             => DEVICE
        )
        port map (
            CLK                     => APP_CLK,
            RESET                   => APP_RESET(1),

            DMA_RX_MVB_LEN          => app_dma_rx_mvb_len_deser(i),
            DMA_RX_MVB_HDR_META     => app_dma_rx_mvb_hdr_meta_deser(i),
            DMA_RX_MVB_CHANNEL      => app_dma_rx_mvb_channel_mod(i),
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
            DMA_TX_MVB_CHANNEL      => app_dma_tx_mvb_channel_mod(i),
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
            MI_DRDY                 => split_mi_drdy(i),

            MEM_CLK                 => MEM_CLK(2*i+1 downto 2*i),
            MEM_RST                 => MEM_RST(2*i+1 downto 2*i),

            MEM_AVMM_READY         => int_avmm_ready(2*i+1 downto 2*i),
            MEM_AVMM_READ          => int_avmm_read(2*i+1 downto 2*i),
            MEM_AVMM_WRITE         => int_avmm_write(2*i+1 downto 2*i),
            MEM_AVMM_ADDRESS       => int_avmm_address(2*i+1 downto 2*i),
            MEM_AVMM_BURSTCOUNT    => int_avmm_burstcount(2*i+1 downto 2*i),
            MEM_AVMM_WRITEDATA     => int_avmm_writedata(2*i+1 downto 2*i),
            MEM_AVMM_READDATA      => int_avmm_readdata(2*i+1 downto 2*i),
            MEM_AVMM_READDATAVALID => int_avmm_readdatavalid(2*i+1 downto 2*i)
        );

        -- In the case of 1 DMA Stream and multiple APP streams (typically ETH
        -- streams), APP_DMA_CHAN_MOD divides the DMA channels between the APP
        -- streams and adjusts signal widths accordingly.
        chan_mod_i : entity work.APP_DMA_CHAN_MOD
        generic map (
            MFB_REGIONS     => MFB_REGIONS,
            DMA_RX_CHANNELS => DMA_RX_CHANNELS,
            DMA_TX_CHANNELS => DMA_TX_CHANNELS,
            DIVIDER         => APP_ST_PER_DMA_ST,
            STREAM_ID       => i,
            ENABLE_MOD      => (CORE_DMA_RX_CHAN /= DMA_RX_CHANNELS)
        )
        port map (
            APP_RX_MVB_CHANNEL => app_dma_rx_mvb_channel_mod(i),
            DMA_RX_MVB_CHANNEL => app_dma_rx_mvb_channel_deser(i),
            APP_TX_MVB_CHANNEL => app_dma_tx_mvb_channel_mod(i),
            DMA_TX_MVB_CHANNEL => app_dma_tx_mvb_channel_deser(i)
        );
    end generate;

    -- =========================================================================
    --  DMA MODULE(S) CONNECTION
    -- =========================================================================

    -- Implements splitting multiple APP streams (typically ETH streams) into
    -- one RX DMA stream and splitting one TX stream between multiple APP
    -- streams according to the upper bits of the DMA channel number.
    streams_merger_i : entity work.APP_DMA_STREAMS_MERGER
    generic map (
        APP_STREAMS           => ETH_STREAMS,
        DMA_STREAMS           => DMA_STREAMS,
        MFB_REGIONS           => MFB_REGIONS,
        MFB_REG_SIZE          => MFB_REG_SIZE,
        MFB_BLOCK_SIZE        => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH        => MFB_ITEM_WIDTH,
        DMA_RX_FRAME_SIZE_MAX => DMA_RX_FRAME_SIZE_MAX,
        DMA_TX_FRAME_SIZE_MAX => DMA_TX_FRAME_SIZE_MAX,
        DMA_RX_CHANNELS       => DMA_RX_CHANNELS,
        DMA_TX_CHANNELS       => DMA_TX_CHANNELS,
        DMA_HDR_META_WIDTH    => DMA_HDR_META_WIDTH,
        DEVICE                => DEVICE
    )
    port map (
        CLK                     => APP_CLK,
        RESET                   => APP_RESET(2),

        APP_DMA_RX_MVB_LEN      => app_dma_rx_mvb_len_deser,
        APP_DMA_RX_MVB_HDR_META => app_dma_rx_mvb_hdr_meta_deser,
        APP_DMA_RX_MVB_CHANNEL  => app_dma_rx_mvb_channel_deser,
        APP_DMA_RX_MVB_DISCARD  => app_dma_rx_mvb_discard_deser,
        APP_DMA_RX_MVB_VLD      => app_dma_rx_mvb_vld_deser,
        APP_DMA_RX_MVB_SRC_RDY  => app_dma_rx_mvb_src_rdy_deser,
        APP_DMA_RX_MVB_DST_RDY  => app_dma_rx_mvb_dst_rdy_deser,

        APP_DMA_RX_MFB_DATA     => app_dma_rx_mfb_data_deser,
        APP_DMA_RX_MFB_SOF      => app_dma_rx_mfb_sof_deser,
        APP_DMA_RX_MFB_EOF      => app_dma_rx_mfb_eof_deser,
        APP_DMA_RX_MFB_SOF_POS  => app_dma_rx_mfb_sof_pos_deser,
        APP_DMA_RX_MFB_EOF_POS  => app_dma_rx_mfb_eof_pos_deser,
        APP_DMA_RX_MFB_SRC_RDY  => app_dma_rx_mfb_src_rdy_deser,
        APP_DMA_RX_MFB_DST_RDY  => app_dma_rx_mfb_dst_rdy_deser,

        DMA_RX_MVB_LEN          => dma_rx_mvb_len_deser,
        DMA_RX_MVB_HDR_META     => dma_rx_mvb_hdr_meta_deser,
        DMA_RX_MVB_CHANNEL      => dma_rx_mvb_channel_deser,
        DMA_RX_MVB_DISCARD      => dma_rx_mvb_discard_deser,
        DMA_RX_MVB_VLD          => dma_rx_mvb_vld_deser,
        DMA_RX_MVB_SRC_RDY      => dma_rx_mvb_src_rdy_deser,
        DMA_RX_MVB_DST_RDY      => dma_rx_mvb_dst_rdy_deser,

        DMA_RX_MFB_DATA         => dma_rx_mfb_data_deser,
        DMA_RX_MFB_SOF          => dma_rx_mfb_sof_deser,
        DMA_RX_MFB_EOF          => dma_rx_mfb_eof_deser,
        DMA_RX_MFB_SOF_POS      => dma_rx_mfb_sof_pos_deser,
        DMA_RX_MFB_EOF_POS      => dma_rx_mfb_eof_pos_deser,
        DMA_RX_MFB_SRC_RDY      => dma_rx_mfb_src_rdy_deser,
        DMA_RX_MFB_DST_RDY      => dma_rx_mfb_dst_rdy_deser,

        DMA_TX_MVB_LEN          => dma_tx_mvb_len_deser,
        DMA_TX_MVB_HDR_META     => dma_tx_mvb_hdr_meta_deser,
        DMA_TX_MVB_CHANNEL      => dma_tx_mvb_channel_deser,
        DMA_TX_MVB_VLD          => dma_tx_mvb_vld_deser,
        DMA_TX_MVB_SRC_RDY      => dma_tx_mvb_src_rdy_deser,
        DMA_TX_MVB_DST_RDY      => dma_tx_mvb_dst_rdy_deser,

        DMA_TX_MFB_DATA         => dma_tx_mfb_data_deser,
        DMA_TX_MFB_SOF          => dma_tx_mfb_sof_deser,
        DMA_TX_MFB_EOF          => dma_tx_mfb_eof_deser,
        DMA_TX_MFB_SOF_POS      => dma_tx_mfb_sof_pos_deser,
        DMA_TX_MFB_EOF_POS      => dma_tx_mfb_eof_pos_deser,
        DMA_TX_MFB_SRC_RDY      => dma_tx_mfb_src_rdy_deser,
        DMA_TX_MFB_DST_RDY      => dma_tx_mfb_dst_rdy_deser,

        APP_DMA_TX_MVB_LEN      => app_dma_tx_mvb_len_deser,
        APP_DMA_TX_MVB_HDR_META => app_dma_tx_mvb_hdr_meta_deser,
        APP_DMA_TX_MVB_CHANNEL  => app_dma_tx_mvb_channel_deser,
        APP_DMA_TX_MVB_VLD      => app_dma_tx_mvb_vld_deser,
        APP_DMA_TX_MVB_SRC_RDY  => app_dma_tx_mvb_src_rdy_deser,
        APP_DMA_TX_MVB_DST_RDY  => app_dma_tx_mvb_dst_rdy_deser,

        APP_DMA_TX_MFB_DATA     => app_dma_tx_mfb_data_deser,
        APP_DMA_TX_MFB_SOF      => app_dma_tx_mfb_sof_deser,
        APP_DMA_TX_MFB_EOF      => app_dma_tx_mfb_eof_deser,
        APP_DMA_TX_MFB_SOF_POS  => app_dma_tx_mfb_sof_pos_deser,
        APP_DMA_TX_MFB_EOF_POS  => app_dma_tx_mfb_eof_pos_deser,
        APP_DMA_TX_MFB_SRC_RDY  => app_dma_tx_mfb_src_rdy_deser,
        APP_DMA_TX_MFB_DST_RDY  => app_dma_tx_mfb_dst_rdy_deser
    );

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
    -- AVMM BRAM (simulation only)
    -- =========================================================================
    bram_g : if MEM_TARGET = MEM_TGT_BRAM generate
        avmm_bram_g : for p in 0 to MEM_PORTS-1 generate
            avmm_bram_i : entity work.AVMM_BRAM
            generic map (
                ADDR_WIDTH  => BRAM_ADDR_WIDTH,
                BURST_WIDTH => MEM_BURST_WIDTH,
                DATA_WIDTH  => MEM_DATA_WIDTH,
                DEVICE      => DEVICE
            )
            port map (
                CLK                 => MEM_CLK(p),
                RESET               => MEM_RST(p),

                AVMM_READY          => int_avmm_ready(p),
                AVMM_READ           => int_avmm_read(p),
                AVMM_WRITE          => int_avmm_write(p),
                AVMM_ADDRESS        => resize(int_avmm_address(p), BRAM_ADDR_WIDTH),
                AVMM_BURSTCOUNT     => int_avmm_burstcount(p),
                AVMM_WRITEDATA      => int_avmm_writedata(p),

                AVMM_READDATA       => int_avmm_readdata(p),
                AVMM_READDATAVALID  => int_avmm_readdatavalid(p)
            );
        end generate;
    end generate;

    ext_g : if MEM_TARGET = MEM_TGT_EXT_DDR generate
        syn_ports_g : for i in 0 to MEM_PORTS-1 generate
            -- Outputs: driven by dram_fifo component
            MEM_AVMM_READ(i)          <= int_avmm_read(i);
            MEM_AVMM_WRITE(i)         <= int_avmm_write(i);
            MEM_AVMM_ADDRESS(i)       <= int_avmm_address(i);
            MEM_AVMM_BURSTCOUNT(i)    <= int_avmm_burstcount(i);
            MEM_AVMM_WRITEDATA(i)     <= int_avmm_writedata(i);

            -- Inputs: external memory controller drives these signals
            int_avmm_ready(i)         <= MEM_AVMM_READY(i);
            int_avmm_readdata(i)      <= MEM_AVMM_READDATA(i);
            int_avmm_readdatavalid(i) <= MEM_AVMM_READDATAVALID(i);
        end generate;
    end generate;
end architecture;
