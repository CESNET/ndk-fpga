-- app_subcore.vhd: User application subcore
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;
use work.combo_user_const.all;

entity APP_SUBCORE is
generic (
    -- MFB parameters
    MFB_REGIONS        : integer := 1;  -- Number of regions in word
    MFB_REG_SIZE       : integer := 8;  -- Number of blocks in region
    MFB_BLOCK_SIZE     : integer := 8;  -- Number of items in block
    MFB_ITEM_WIDTH     : integer := 8;  -- Width of one item in bits
    MI_ADDR_WIDTH      : integer := 32;
    MI_DATA_WIDTH      : integer := 32;
    -- ID number of this subcore instance
    SUBCORE_ID         : natural := 0;
    -- Number of Ethernet channels mapped to this subcore
    ETH_CHANNELS       : natural := 1;
    -- Maximum size of a User packet (in bytes)
    -- Defines width of Packet length signals.
    USR_PKT_SIZE_MAX   : natural := 2**12;
    -- Number of streams from DMA module
    DMA_RX_CHANNELS    : integer;
    DMA_TX_CHANNELS    : integer;
    -- Width of TX User Header Metadata information extracted from descriptor
    DMA_HDR_META_WIDTH : natural := 12;
    DEVICE             : string
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK      : in  std_logic;
    RESET    : in  std_logic;
    
    -- =========================================================================
    --  DMA INTERFACES
    -- =========================================================================
    
    -- MFB+MVB interface to DMA module (to software)
    -- -------------------------------------------------------------------------
    DMA_RX_MVB_LEN           : out std_logic_vector(MFB_REGIONS*log2(USR_PKT_SIZE_MAX+1)-1 downto 0);
    DMA_RX_MVB_HDR_META      : out std_logic_vector(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    DMA_RX_MVB_CHANNEL       : out std_logic_vector(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    DMA_RX_MVB_DISCARD       : out std_logic_vector(MFB_REGIONS-1 downto 0);
    -- =======================================
    DMA_RX_MVB_VLD           : out std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_RX_MVB_SRC_RDY       : out std_logic;
    DMA_RX_MVB_DST_RDY       : in  std_logic;
    -- MFB interface with data packets
    DMA_RX_MFB_DATA          : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    DMA_RX_MFB_SOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_RX_MFB_EOF           : out std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_RX_MFB_SOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    DMA_RX_MFB_EOF_POS       : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    DMA_RX_MFB_SRC_RDY       : out std_logic;
    DMA_RX_MFB_DST_RDY       : in  std_logic;
    
    -- MFB+MVB interface from DMA module (from software)
    -- -------------------------------------------------------------------------
    -- MVB interface (aligned to SOF)
    -- TX_USR_MVB_DATA =======================
    DMA_TX_MVB_LEN          : in  std_logic_vector(MFB_REGIONS*log2(USR_PKT_SIZE_MAX+1)-1 downto 0);
    DMA_TX_MVB_HDR_META     : in  std_logic_vector(MFB_REGIONS*DMA_HDR_META_WIDTH-1 downto 0);
    DMA_TX_MVB_CHANNEL      : in  std_logic_vector(MFB_REGIONS*log2(DMA_TX_CHANNELS)-1 downto 0);
    -- =======================================
    DMA_TX_MVB_VLD          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_TX_MVB_SRC_RDY      : in  std_logic;
    DMA_TX_MVB_DST_RDY      : out std_logic;
    -- MFB interface with data packets
    DMA_TX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    DMA_TX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_TX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    DMA_TX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    DMA_TX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    DMA_TX_MFB_SRC_RDY      : in  std_logic;
    DMA_TX_MFB_DST_RDY      : out std_logic;

    -- =========================================================================
    --  ETH INTERFACES
    -- =========================================================================
    
    -- MFB+MVB interface with incoming network packets
    -- -------------------------------------------------------------------------
    -- MVB interface with packet headers (aligned to EOF)
    ETH_RX_MVB_DATA         : in  std_logic_vector(MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    ETH_RX_MVB_VLD          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    ETH_RX_MVB_SRC_RDY      : in  std_logic;
    ETH_RX_MVB_DST_RDY      : out std_logic;
    -- MFB interface with data packets
    ETH_RX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    ETH_RX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    ETH_RX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    ETH_RX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    ETH_RX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    ETH_RX_MFB_SRC_RDY      : in  std_logic;
    ETH_RX_MFB_DST_RDY      : out std_logic;

    -- MFB+MVB interface with outgoing network packets
    -- -------------------------------------------------------------------------
    -- MFB interface with data packets + header
    ETH_TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    ETH_TX_MFB_HDR          : out std_logic_vector(MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0) := (others => '0'); -- valid with SOF
    ETH_TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
    ETH_TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
    ETH_TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    ETH_TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    ETH_TX_MFB_SRC_RDY      : out std_logic;
    ETH_TX_MFB_DST_RDY      : in  std_logic;
    
    -- =========================================================================
    --  MI INTERFACE
    -- =========================================================================
    MI_DWR                  : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR                 : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_BE                   : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_RD                   : in  std_logic;
    MI_WR                   : in  std_logic;
    MI_DRD                  : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY                 : out std_logic;
    MI_DRDY                 : out std_logic
);
end entity;

architecture FULL of APP_SUBCORE is

    constant DMA_TX_PER_ETH_CHAN : natural := DMA_TX_CHANNELS/ETH_CHANNELS;

    signal dma_tx_mvb_len_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(log2(USR_PKT_SIZE_MAX+1)-1 downto 0);
    signal dma_tx_mvb_channel_arr : slv_array_t(MFB_REGIONS-1 downto 0)(log2(DMA_TX_CHANNELS)-1 downto 0);
    signal dma_tx_mvb_ethch_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(log2(ETH_CHANNELS)-1 downto 0);
    signal dma_tx_mvb_ethch2_arr  : u_array_t(MFB_REGIONS-1 downto 0)(ETH_TX_HDR_PORT_W-1 downto 0);
    signal dma_tx_mvb_data_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(ETH_TX_HDR_WIDTH-1 downto 0);

    signal ethi_tx_mfb_data       : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ethi_tx_mfb_hdr        : std_logic_vector(MFB_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0);
    signal ethi_tx_mfb_sof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethi_tx_mfb_eof        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethi_tx_mfb_sof_pos    : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal ethi_tx_mfb_eof_pos    : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ethi_tx_mfb_src_rdy    : std_logic;
    signal ethi_tx_mfb_dst_rdy    : std_logic;

    signal ethp_rx_mvb_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(ETH_RX_HDR_WIDTH-1 downto 0);
    signal ethp_rx_mvb_data       : std_logic_vector(MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal ethp_rx_mvb_chan_arr   : u_array_t(MFB_REGIONS-1 downto 0)(ETH_RX_HDR_PORT_W-1 downto 0);
    signal ethp_rx_mvb_chan2_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(log2(ETH_CHANNELS)-1 downto 0);
    signal ethp_rx_mvb_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethp_rx_mvb_src_rdy    : std_logic;
    signal ethp_rx_mvb_dst_rdy    : std_logic;

    signal ethd_rx_mvb_data_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(ETH_RX_HDR_WIDTH-1 downto 0);
    signal ethd_rx_mvb_data       : std_logic_vector(MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal ethd_rx_mvb_chan       : std_logic_vector(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal ethd_rx_mvb_len_arr    : slv_array_t(MFB_REGIONS-1 downto 0)(log2(USR_PKT_SIZE_MAX+1)-1 downto 0);
    signal ethd_rx_mvb_vld        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethd_rx_mvb_src_rdy    : std_logic;
    signal ethd_rx_mvb_dst_rdy    : std_logic;

begin

    -- =========================================================================
    --  APPLICATION
    -- =========================================================================

    -- ------------------------------------
    -- TX PATH
    -- ------------------------------------
    dma_tx_mvb_len_arr     <= slv_array_deser(DMA_TX_MVB_LEN,MFB_REGIONS);
    dma_tx_mvb_channel_arr <= slv_array_deser(DMA_TX_MVB_CHANNEL,MFB_REGIONS);

    dma_tx_mvb_data_arr_g: for i in 0 to MFB_REGIONS-1 generate
        -- DMA TX to ETH channel mapping: all DMA TX channels are divided into
        -- separate groups for each ETH channel
        eth_ch_one_g: if (ETH_CHANNELS = 1) generate
            -- There is only one ETH channel, all DMA TX channels are mapped to
            -- the ETH channel.
            dma_tx_mvb_ethch_arr(i) <= (others => '0');
        end generate;
        eth_ch_more_g: if (ETH_CHANNELS > 1) generate
            -- Top bits of DMA TX channel number are used as ETH channel number.
            dma_tx_mvb_ethch_arr(i) <= dma_tx_mvb_channel_arr(i)(log2(ETH_CHANNELS)+log2(DMA_TX_PER_ETH_CHAN)-1 downto log2(DMA_TX_PER_ETH_CHAN));
        end generate;
        -- ETH_TX_HDR_PORT is global (over all ETH ports) identification number
        -- for each ETH channel, this logic convert local ETH channel number to
        -- global identification number.
        dma_tx_mvb_ethch2_arr(i) <= resize(unsigned(dma_tx_mvb_ethch_arr(i)),ETH_TX_HDR_PORT_W) + (SUBCORE_ID*ETH_CHANNELS);
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_PORT) <= std_logic_vector(dma_tx_mvb_ethch2_arr(i));
        -- Packet length in bytes
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_LENGTH) <= std_logic_vector(resize(unsigned(dma_tx_mvb_len_arr(i)),ETH_TX_HDR_LENGTH_W));
        -- The discard feature is not currently supported in TX MAX Lite.
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_DISCARD_O) <= '0';
    end generate;

    tx_mvb_ins_i : entity work.METADATA_INSERTOR
    generic map(
        MVB_ITEMS       => MFB_REGIONS,
        MVB_ITEM_WIDTH  => ETH_TX_HDR_WIDTH,
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REG_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        INSERT_MODE     => 0,
        MVB_FIFO_SIZE   => 32,
        DEVICE          => DEVICE
    )
    port map(
        CLK             => CLK,
        RESET           => RESET,

        RX_MVB_DATA     => slv_array_ser(dma_tx_mvb_data_arr),
        RX_MVB_VLD      => DMA_TX_MVB_VLD,
        RX_MVB_SRC_RDY  => DMA_TX_MVB_SRC_RDY,
        RX_MVB_DST_RDY  => DMA_TX_MVB_DST_RDY,
    
        RX_MFB_DATA     => DMA_TX_MFB_DATA,
        RX_MFB_SOF      => DMA_TX_MFB_SOF,
        RX_MFB_EOF      => DMA_TX_MFB_EOF,
        RX_MFB_SOF_POS  => DMA_TX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => DMA_TX_MFB_EOF_POS,
        RX_MFB_SRC_RDY  => DMA_TX_MFB_SRC_RDY,
        RX_MFB_DST_RDY  => DMA_TX_MFB_DST_RDY,
    
        TX_MFB_DATA     => ethi_tx_mfb_data,
        TX_MFB_META_NEW => ethi_tx_mfb_hdr,
        TX_MFB_SOF      => ethi_tx_mfb_sof,
        TX_MFB_EOF      => ethi_tx_mfb_eof,
        TX_MFB_SOF_POS  => ethi_tx_mfb_sof_pos,
        TX_MFB_EOF_POS  => ethi_tx_mfb_eof_pos,
        TX_MFB_SRC_RDY  => ethi_tx_mfb_src_rdy,
        TX_MFB_DST_RDY  => ethi_tx_mfb_dst_rdy
    );

    tx_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REG_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => ETH_TX_HDR_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => ethi_tx_mfb_data,
        RX_META    => ethi_tx_mfb_hdr,
        RX_SOF_POS => ethi_tx_mfb_sof_pos,
        RX_EOF_POS => ethi_tx_mfb_eof_pos,
        RX_SOF     => ethi_tx_mfb_sof,
        RX_EOF     => ethi_tx_mfb_eof,
        RX_SRC_RDY => ethi_tx_mfb_src_rdy,
        RX_DST_RDY => ethi_tx_mfb_dst_rdy,

        TX_DATA    => ETH_TX_MFB_DATA,
        TX_META    => ETH_TX_MFB_HDR,
        TX_SOF_POS => ETH_TX_MFB_SOF_POS,
        TX_EOF_POS => ETH_TX_MFB_EOF_POS,
        TX_SOF     => ETH_TX_MFB_SOF,
        TX_EOF     => ETH_TX_MFB_EOF,
        TX_SRC_RDY => ETH_TX_MFB_SRC_RDY,
        TX_DST_RDY => ETH_TX_MFB_DST_RDY
    );

    -- ------------------------------------
    -- RX HEADER PATH
    -- ------------------------------------
    rx_mvb_pipe_i : entity work.MVB_PIPE
    generic map(
        ITEMS       => MFB_REGIONS,
        ITEM_WIDTH  => ETH_RX_HDR_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => ETH_RX_MVB_DATA,
        RX_VLD     => ETH_RX_MVB_VLD,
        RX_SRC_RDY => ETH_RX_MVB_SRC_RDY,
        RX_DST_RDY => ETH_RX_MVB_DST_RDY,

        TX_DATA    => ethp_rx_mvb_data,
        TX_VLD     => ethp_rx_mvb_vld,
        TX_SRC_RDY => ethp_rx_mvb_src_rdy,
        TX_DST_RDY => ethp_rx_mvb_dst_rdy
    );

    ethp_rx_mvb_data_arr <= slv_array_deser(ethp_rx_mvb_data,MFB_REGIONS);
    ethp_rx_mvb_chan_arr_g: for i in 0 to MFB_REGIONS-1 generate
        -- ETH_RX_HDR_PORT is global (over all ETH ports) identification number
        -- for each ETH channel, this logic computes local ETH channel number.
        ethp_rx_mvb_chan_arr(i)  <= (unsigned(ethp_rx_mvb_data_arr(i)(ETH_RX_HDR_PORT)) - (SUBCORE_ID*ETH_CHANNELS));
        -- Resize MVB channel vector.
        ethp_rx_mvb_chan2_arr(i) <= std_logic_vector(resize(ethp_rx_mvb_chan_arr(i),log2(ETH_CHANNELS)));
    end generate;

    -- DMA channel distribution
    chan_dist_i : entity work.MVB_CHANNEL_ROUTER_MI
    generic map(
        ITEMS        => MFB_REGIONS,
        ITEM_WIDTH   => ETH_RX_HDR_WIDTH,
        SRC_CHANNELS => ETH_CHANNELS,
        DST_CHANNELS => DMA_RX_CHANNELS,
        DEFAULT_MODE => 2,
        OPT_MODE     => True,
        DEVICE       => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        MI_DWR     => MI_DWR,
        MI_ADDR    => MI_ADDR,
        MI_BE      => MI_BE,
        MI_RD      => MI_RD,
        MI_WR      => MI_WR,
        MI_ARDY    => MI_ARDY,
        MI_DRD     => MI_DRD,
        MI_DRDY    => MI_DRDY,

        RX_DATA    => ethp_rx_mvb_data,
        RX_CHANNEL => slv_array_ser(ethp_rx_mvb_chan2_arr),
        RX_VLD     => ethp_rx_mvb_vld,
        RX_SRC_RDY => ethp_rx_mvb_src_rdy,
        RX_DST_RDY => ethp_rx_mvb_dst_rdy,

        TX_DATA    => ethd_rx_mvb_data,
        TX_CHANNEL => ethd_rx_mvb_chan,
        TX_VLD     => ethd_rx_mvb_vld,
        TX_SRC_RDY => ethd_rx_mvb_src_rdy,
        TX_DST_RDY => ethd_rx_mvb_dst_rdy
    );

    ethd_rx_mvb_data_arr <= slv_array_deser(ethd_rx_mvb_data,MFB_REGIONS);
    ethd_rx_mvb_len_arr_g: for i in 0 to MFB_REGIONS-1 generate
        ethd_rx_mvb_len_arr(i) <= std_logic_vector(resize(unsigned(ethd_rx_mvb_data_arr(i)(ETH_RX_HDR_LENGTH)),log2(USR_PKT_SIZE_MAX+1)));
    end generate;

    DMA_RX_MVB_LEN      <= slv_array_ser(ethd_rx_mvb_len_arr);
    DMA_RX_MVB_HDR_META <= (others => '0');
    DMA_RX_MVB_CHANNEL  <= ethd_rx_mvb_chan;
    DMA_RX_MVB_DISCARD  <= (others => '0');
    DMA_RX_MVB_VLD      <= ethd_rx_mvb_vld;
    DMA_RX_MVB_SRC_RDY  <= ethd_rx_mvb_src_rdy;
    ethd_rx_mvb_dst_rdy <= DMA_RX_MVB_DST_RDY;

    -- ------------------------------------
    -- RX DATA PATH
    -- ------------------------------------

    rx_mfb_pipe_i : entity work.MFB_PIPE
    generic map(
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REG_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => 1,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => ETH_RX_MFB_DATA,
        RX_META    => (others => '0'),
        RX_SOF_POS => ETH_RX_MFB_SOF_POS,
        RX_EOF_POS => ETH_RX_MFB_EOF_POS,
        RX_SOF     => ETH_RX_MFB_SOF,
        RX_EOF     => ETH_RX_MFB_EOF,
        RX_SRC_RDY => ETH_RX_MFB_SRC_RDY,
        RX_DST_RDY => ETH_RX_MFB_DST_RDY,

        TX_DATA    => DMA_RX_MFB_DATA,
        TX_META    => open,
        TX_SOF_POS => DMA_RX_MFB_SOF_POS,
        TX_EOF_POS => DMA_RX_MFB_EOF_POS,
        TX_SOF     => DMA_RX_MFB_SOF,
        TX_EOF     => DMA_RX_MFB_EOF,
        TX_SRC_RDY => DMA_RX_MFB_SRC_RDY,
        TX_DST_RDY => DMA_RX_MFB_DST_RDY
    );

end architecture;
