-- app_dma_streams_merger.vhd: Application DMA streams merger/splitter
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity APP_DMA_STREAMS_MERGER is
generic (
    APP_STREAMS           : natural := 2;  -- must be power of two
    DMA_STREAMS           : natural := 1;  -- must be 1
    -- MFB parameters
    MFB_REGIONS           : natural := 1;  -- Number of regions in word
    MFB_REG_SIZE          : natural := 8;  -- Number of blocks in region
    MFB_BLOCK_SIZE        : natural := 8;  -- Number of items in block
    MFB_ITEM_WIDTH        : natural := 8;  -- Width of one item in bits
    -- Maximum size of a DMA RX frame (in bytes)
    DMA_RX_FRAME_SIZE_MAX : natural := 2**12;
    -- Maximum size of a DMA TX frame (in bytes)
    DMA_TX_FRAME_SIZE_MAX : natural := 2**12;
    -- Number of streams from DMA module
    DMA_RX_CHANNELS       : natural := 8;
    DMA_TX_CHANNELS       : natural := 8;
    -- Width of TX User Header Metadata information extracted from descriptor
    DMA_HDR_META_WIDTH    : natural := 12;
    DEVICE                : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK      : in  std_logic;
    RESET    : in  std_logic;
    
    -- =========================================================================
    --  APP2DMA PATH
    -- =========================================================================

    -- MFB+MVB interface to DMA module (from APP/ETH module)
    -- -------------------------------------------------------------------------
    APP_DMA_RX_MVB_LEN      : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    APP_DMA_RX_MVB_HDR_META : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    APP_DMA_RX_MVB_CHANNEL  : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    APP_DMA_RX_MVB_DISCARD  : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_RX_MVB_VLD      : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_RX_MVB_SRC_RDY  : in  std_logic_vector(APP_STREAMS-1 downto 0);
    APP_DMA_RX_MVB_DST_RDY  : out std_logic_vector(APP_STREAMS-1 downto 0);
    -- MFB interface with data packets
    APP_DMA_RX_MFB_DATA     : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    APP_DMA_RX_MFB_SOF      : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_RX_MFB_EOF      : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_RX_MFB_SOF_POS  : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    APP_DMA_RX_MFB_EOF_POS  : in  slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    APP_DMA_RX_MFB_SRC_RDY  : in  std_logic_vector(APP_STREAMS-1 downto 0);
    APP_DMA_RX_MFB_DST_RDY  : out std_logic_vector(APP_STREAMS-1 downto 0);
    
    -- MFB+MVB interface to DMA module (to DMA module)
    -- -------------------------------------------------------------------------
    DMA_RX_MVB_LEN          : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto 0);
    DMA_RX_MVB_HDR_META     : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    DMA_RX_MVB_CHANNEL      : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    DMA_RX_MVB_DISCARD      : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_RX_MVB_VLD          : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_RX_MVB_SRC_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);
    DMA_RX_MVB_DST_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);
    -- MFB interface with data packets
    DMA_RX_MFB_DATA         : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    DMA_RX_MFB_SOF          : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_RX_MFB_EOF          : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_RX_MFB_SOF_POS      : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    DMA_RX_MFB_EOF_POS      : out slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    DMA_RX_MFB_SRC_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);
    DMA_RX_MFB_DST_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =========================================================================
    --  DMA2APP PATH
    -- =========================================================================

    -- MFB+MVB interface to DMA module (from DMA module)
    -- -------------------------------------------------------------------------
    DMA_TX_MVB_LEN          : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    DMA_TX_MVB_HDR_META     : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    DMA_TX_MVB_CHANNEL      : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    DMA_TX_MVB_VLD          : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_TX_MVB_SRC_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);
    DMA_TX_MVB_DST_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);
    -- MFB interface with data packets
    DMA_TX_MFB_DATA         : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    DMA_TX_MFB_SOF          : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_TX_MFB_EOF          : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    DMA_TX_MFB_SOF_POS      : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    DMA_TX_MFB_EOF_POS      : in  slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    DMA_TX_MFB_SRC_RDY      : in  std_logic_vector(DMA_STREAMS-1 downto 0);
    DMA_TX_MFB_DST_RDY      : out std_logic_vector(DMA_STREAMS-1 downto 0);
    
    -- MFB+MVB interface to DMA module (to APP/ETH module)
    -- -------------------------------------------------------------------------
    APP_DMA_TX_MVB_LEN      : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto 0);
    APP_DMA_TX_MVB_HDR_META : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    APP_DMA_TX_MVB_CHANNEL  : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    APP_DMA_TX_MVB_VLD      : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_TX_MVB_SRC_RDY  : out std_logic_vector(APP_STREAMS-1 downto 0);
    APP_DMA_TX_MVB_DST_RDY  : in  std_logic_vector(APP_STREAMS-1 downto 0);
    -- MFB interface with data packets
    APP_DMA_TX_MFB_DATA     : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    APP_DMA_TX_MFB_SOF      : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_TX_MFB_EOF      : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    APP_DMA_TX_MFB_SOF_POS  : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    APP_DMA_TX_MFB_EOF_POS  : out slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    APP_DMA_TX_MFB_SRC_RDY  : out std_logic_vector(APP_STREAMS-1 downto 0);
    APP_DMA_TX_MFB_DST_RDY  : in  std_logic_vector(APP_STREAMS-1 downto 0)
);
end entity;

architecture FULL of APP_DMA_STREAMS_MERGER is

    constant DMA_RX_ALL_META_W : natural := log2(DMA_RX_FRAME_SIZE_MAX+1) + DMA_HDR_META_WIDTH + log2(DMA_RX_CHANNELS) + 1;
    constant DMA_TX_ALL_META_W : natural := log2(DMA_TX_FRAME_SIZE_MAX+1) + DMA_HDR_META_WIDTH + log2(DMA_TX_CHANNELS);

    signal app_dma_rx_mvb_data_deser     : slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*DMA_RX_ALL_META_W-1 downto 0);
    signal app_dma_rx_mvb_payload_deser  : slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal app_dma_tx_mvb_data_deser     : slv_array_t(APP_STREAMS-1 downto 0)(MFB_REGIONS*DMA_TX_ALL_META_W-1 downto 0);

    signal dma_rx_mvb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_RX_ALL_META_W-1 downto 0);
    signal dma_tx_mvb_data_deser         : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*DMA_TX_ALL_META_W-1 downto 0);
    signal dma_tx_mvb_switch_deser       : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS*log2(APP_STREAMS)-1 downto 0);
    signal dma_tx_mvb_payload_deser      : slv_array_t(DMA_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);

begin

    assert ((DMA_STREAMS = APP_STREAMS) or (DMA_STREAMS < APP_STREAMS and DMA_STREAMS = 1))
        report "APP_STREAMS_MERGER: The number of DMA_STREAMS must be equal to APP_STREAMS, or DMA_STREAMS must be 1 and DMA_STREAMS < APP_STREAMS!"
        severity failure;

    -- simple connection
    dma2app_eq_g: if (DMA_STREAMS = APP_STREAMS) generate
        DMA_RX_MVB_LEN          <= APP_DMA_RX_MVB_LEN;
        DMA_RX_MVB_HDR_META     <= APP_DMA_RX_MVB_HDR_META;
        DMA_RX_MVB_CHANNEL      <= APP_DMA_RX_MVB_CHANNEL;
        DMA_RX_MVB_DISCARD      <= APP_DMA_RX_MVB_DISCARD;
        DMA_RX_MVB_VLD          <= APP_DMA_RX_MVB_VLD;
        DMA_RX_MVB_SRC_RDY      <= APP_DMA_RX_MVB_SRC_RDY;
        APP_DMA_RX_MVB_DST_RDY  <= DMA_RX_MVB_DST_RDY;

        DMA_RX_MFB_DATA         <= APP_DMA_RX_MFB_DATA;
        DMA_RX_MFB_SOF_POS      <= APP_DMA_RX_MFB_SOF_POS;
        DMA_RX_MFB_EOF_POS      <= APP_DMA_RX_MFB_EOF_POS;
        DMA_RX_MFB_SOF          <= APP_DMA_RX_MFB_SOF;
        DMA_RX_MFB_EOF          <= APP_DMA_RX_MFB_EOF;
        DMA_RX_MFB_SRC_RDY      <= APP_DMA_RX_MFB_SRC_RDY;
        APP_DMA_RX_MFB_DST_RDY  <= DMA_RX_MFB_DST_RDY;

        APP_DMA_TX_MVB_LEN      <= DMA_TX_MVB_LEN;
        APP_DMA_TX_MVB_HDR_META <= DMA_TX_MVB_HDR_META;
        APP_DMA_TX_MVB_CHANNEL  <= DMA_TX_MVB_CHANNEL;
        APP_DMA_TX_MVB_VLD      <= DMA_TX_MVB_VLD;
        APP_DMA_TX_MVB_SRC_RDY  <= DMA_TX_MVB_SRC_RDY;
        DMA_TX_MVB_DST_RDY      <= APP_DMA_TX_MVB_DST_RDY;

        APP_DMA_TX_MFB_DATA     <= DMA_TX_MFB_DATA;
        APP_DMA_TX_MFB_SOF_POS  <= DMA_TX_MFB_SOF_POS;
        APP_DMA_TX_MFB_EOF_POS  <= DMA_TX_MFB_EOF_POS;
        APP_DMA_TX_MFB_SOF      <= DMA_TX_MFB_SOF;
        APP_DMA_TX_MFB_EOF      <= DMA_TX_MFB_EOF;
        APP_DMA_TX_MFB_SRC_RDY  <= DMA_TX_MFB_SRC_RDY;
        DMA_TX_MFB_DST_RDY      <= APP_DMA_TX_MFB_DST_RDY;
    end generate;

    -- merge each ETH stream to single DMA stream
    dma2app_one_g: if (DMA_STREAMS < APP_STREAMS and DMA_STREAMS = 1) generate

        -- =========================================================================
        -- APP2DMA PATH
        -- =========================================================================

        -- pack MVB data (APP2DMA)
        app_dma_rx_mvb_data_g: for i in 0 to APP_STREAMS-1 generate
            app_dma_rx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W)                                                                                                 <= APP_DMA_RX_MVB_DISCARD(i)(r);
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W+1)                                          <= APP_DMA_RX_MVB_CHANNEL(i)((r+1)*log2(DMA_RX_CHANNELS)-1 downto r*log2(DMA_RX_CHANNELS));
                app_dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)) <= APP_DMA_RX_MVB_HDR_META(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH);
                app_dma_rx_mvb_data_deser(i)((r+1)*DMA_RX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH)                     <= APP_DMA_RX_MVB_LEN(i)((r+1)*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto r*log2(DMA_RX_FRAME_SIZE_MAX+1));
            end generate;
        end generate;

        app_dma_rx_mvb_payload_deser <= (others => (others => '1'));

        mfb_merger_tree_i : entity work.MFB_MERGER_GEN
        generic map(
            MERGER_INPUTS   => APP_STREAMS,
            MVB_ITEMS       => MFB_REGIONS,
            MVB_ITEM_WIDTH  => DMA_RX_ALL_META_W,
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REG_SIZE    => MFB_REG_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            INPUT_FIFO_SIZE => 32,
            RX_PAYLOAD_EN   => (others => true),
            IN_PIPE_EN      => false,
            OUT_PIPE_EN     => true,
            DEVICE          => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,
                
            RX_MVB_DATA     => app_dma_rx_mvb_data_deser,
            RX_MVB_PAYLOAD  => app_dma_rx_mvb_payload_deser,
            RX_MVB_VLD      => APP_DMA_RX_MVB_VLD,
            RX_MVB_SRC_RDY  => APP_DMA_RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => APP_DMA_RX_MVB_DST_RDY,

            RX_MFB_DATA     => APP_DMA_RX_MFB_DATA,
            RX_MFB_SOF      => APP_DMA_RX_MFB_SOF,
            RX_MFB_EOF      => APP_DMA_RX_MFB_EOF,
            RX_MFB_SOF_POS  => APP_DMA_RX_MFB_SOF_POS,
            RX_MFB_EOF_POS  => APP_DMA_RX_MFB_EOF_POS,
            RX_MFB_SRC_RDY  => APP_DMA_RX_MFB_SRC_RDY,
            RX_MFB_DST_RDY  => APP_DMA_RX_MFB_DST_RDY,

            TX_MVB_DATA     => dma_rx_mvb_data_deser(0),
            TX_MVB_VLD      => DMA_RX_MVB_VLD(0),
            TX_MVB_SRC_RDY  => DMA_RX_MVB_SRC_RDY(0),
            TX_MVB_DST_RDY  => DMA_RX_MVB_DST_RDY(0),

            TX_MFB_DATA     => DMA_RX_MFB_DATA(0),
            TX_MFB_SOF      => DMA_RX_MFB_SOF(0),
            TX_MFB_EOF      => DMA_RX_MFB_EOF(0),
            TX_MFB_SOF_POS  => DMA_RX_MFB_SOF_POS(0),
            TX_MFB_EOF_POS  => DMA_RX_MFB_EOF_POS(0),
            TX_MFB_SRC_RDY  => DMA_RX_MFB_SRC_RDY(0),
            TX_MFB_DST_RDY  => DMA_RX_MFB_DST_RDY(0)
        );

        -- unpack MVB data (APP2DMA)
        dma_rx_mvb_data_g: for i in 0 to DMA_STREAMS-1 generate
            dma_rx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                DMA_RX_MVB_DISCARD(i)(r)                                                            <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W);
                DMA_RX_MVB_CHANNEL(i)((r+1)*log2(DMA_RX_CHANNELS)-1 downto r*log2(DMA_RX_CHANNELS)) <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)-1 downto r*DMA_RX_ALL_META_W+1);
                DMA_RX_MVB_HDR_META(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH)      <= dma_rx_mvb_data_deser(i)(r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS));
                DMA_RX_MVB_LEN(i)((r+1)*log2(DMA_RX_FRAME_SIZE_MAX+1)-1 downto r*log2(DMA_RX_FRAME_SIZE_MAX+1)) <= dma_rx_mvb_data_deser(i)((r+1)*DMA_RX_ALL_META_W-1 downto r*DMA_RX_ALL_META_W+1+log2(DMA_RX_CHANNELS)+DMA_HDR_META_WIDTH);
            end generate;
        end generate;

        -- =========================================================================
        -- DMA2APP PATH
        -- =========================================================================

        -- pack MVB data (DMA2APP)
        dma_tx_mvb_data_g: for i in 0 to DMA_STREAMS-1 generate
            dma_tx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)-1 downto r*DMA_TX_ALL_META_W)                                          <= DMA_TX_MVB_CHANNEL(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto r*log2(DMA_TX_CHANNELS));
                dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)) <= DMA_TX_MVB_HDR_META(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH);
                dma_tx_mvb_data_deser(i)((r+1)*DMA_TX_ALL_META_W-1 downto r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH)                   <= DMA_TX_MVB_LEN(i)((r+1)*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto r*log2(DMA_TX_FRAME_SIZE_MAX+1));

                dma_tx_mvb_switch_deser(i)((r+1)*log2(APP_STREAMS)-1 downto r*log2(APP_STREAMS)) <= DMA_TX_MVB_CHANNEL(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto (r+1)*log2(DMA_TX_CHANNELS)-log2(APP_STREAMS));
            end generate;
        end generate;

        dma_tx_mvb_payload_deser <= (others => (others => '1'));

        mfb_splitter_tree_i : entity work.MFB_SPLITTER_GEN
        generic map(
            SPLITTER_OUTPUTS => APP_STREAMS,
            MVB_ITEMS        => MFB_REGIONS,
            MVB_ITEM_WIDTH   => DMA_TX_ALL_META_W,
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REG_SIZE     => MFB_REG_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
            OUTPUT_FIFO_SIZE => 32,
            OUT_PIPE_EN      => true,
            DEVICE           => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_DATA     => dma_tx_mvb_data_deser(0),
            RX_MVB_SWITCH   => dma_tx_mvb_switch_deser(0),
            RX_MVB_PAYLOAD  => dma_tx_mvb_payload_deser(0),
            RX_MVB_VLD      => DMA_TX_MVB_VLD(0),
            RX_MVB_SRC_RDY  => DMA_TX_MVB_SRC_RDY(0),
            RX_MVB_DST_RDY  => DMA_TX_MVB_DST_RDY(0),

            RX_MFB_DATA     => DMA_TX_MFB_DATA(0),
            RX_MFB_SOF      => DMA_TX_MFB_SOF(0),
            RX_MFB_EOF      => DMA_TX_MFB_EOF(0),
            RX_MFB_SOF_POS  => DMA_TX_MFB_SOF_POS(0),
            RX_MFB_EOF_POS  => DMA_TX_MFB_EOF_POS(0),
            RX_MFB_SRC_RDY  => DMA_TX_MFB_SRC_RDY(0),
            RX_MFB_DST_RDY  => DMA_TX_MFB_DST_RDY(0),

            TX_MVB_DATA     => app_dma_tx_mvb_data_deser,
            TX_MVB_VLD      => APP_DMA_TX_MVB_VLD,
            TX_MVB_SRC_RDY  => APP_DMA_TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => APP_DMA_TX_MVB_DST_RDY,

            TX_MFB_DATA     => APP_DMA_TX_MFB_DATA,
            TX_MFB_SOF      => APP_DMA_TX_MFB_SOF,
            TX_MFB_EOF      => APP_DMA_TX_MFB_EOF,
            TX_MFB_SOF_POS  => APP_DMA_TX_MFB_SOF_POS,
            TX_MFB_EOF_POS  => APP_DMA_TX_MFB_EOF_POS,
            TX_MFB_SRC_RDY  => APP_DMA_TX_MFB_SRC_RDY,
            TX_MFB_DST_RDY  => APP_DMA_TX_MFB_DST_RDY
        );

        -- unpack MVB data (DMA2APP)
        app_dma_tx_mvb_data_g: for i in 0 to APP_STREAMS-1 generate
            app_dma_tx_mvb_data_g2: for r in 0 to MFB_REGIONS-1 generate
                APP_DMA_TX_MVB_CHANNEL(i)((r+1)*log2(DMA_TX_CHANNELS)-1 downto r*log2(DMA_TX_CHANNELS)) <= app_dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)-1 downto r*DMA_TX_ALL_META_W);
                APP_DMA_TX_MVB_HDR_META(i)((r+1)*DMA_HDR_META_WIDTH-1 downto r*DMA_HDR_META_WIDTH)      <= app_dma_tx_mvb_data_deser(i)(r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH-1 downto r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS));
                APP_DMA_TX_MVB_LEN(i)((r+1)*log2(DMA_TX_FRAME_SIZE_MAX+1)-1 downto r*log2(DMA_TX_FRAME_SIZE_MAX+1)) <= app_dma_tx_mvb_data_deser(i)((r+1)*DMA_TX_ALL_META_W-1 downto r*DMA_TX_ALL_META_W+log2(DMA_TX_CHANNELS)+DMA_HDR_META_WIDTH);
            end generate;
        end generate;
    end generate;

end architecture;
