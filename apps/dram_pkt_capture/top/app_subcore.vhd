-- app_subcore.vhd: User application subcore
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal    <cabal@cesnet.cz>
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

entity APP_SUBCORE is
    generic (
        -- MFB parameters
        MFB_REGIONS        : integer := 1;  -- Number of regions in word
        MFB_REG_SIZE       : integer := 8;  -- Number of blocks in region
        MFB_BLOCK_SIZE     : integer := 8;  -- Number of items in block
        MFB_ITEM_WIDTH     : integer := 8;  -- Width of one item in bits
        MI_ADDR_WIDTH      : integer := 32;
        MI_DATA_WIDTH      : integer := 32;

        MEM_ADDR_WIDTH  : natural := 27;
        RING_ADDR_WIDTH : natural := 27;
        MEM_BURST_WIDTH : natural := 7;
        -- n6010 has 4 ports each 256b wide
        MEM_DATA_WIDTH  : natural := 256;

        -- each subcore uses 2 ports (2x256)
        MEM_PORTS_USED  : natural := 2;

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

        -- Per port memory clk and rst
        MEM_CLK : in std_logic_vector(MEM_PORTS_USED-1 downto 0);
        MEM_RST : in std_logic_vector(MEM_PORTS_USED-1 downto 0);

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
        MI_DRDY                 : out std_logic;

        -- =========================================================================
        --  AVMM INTERFACE
        -- =========================================================================
        -- each subcore has 2 ports
        MEM_AVMM_READY         : in  std_logic_vector(MEM_PORTS_USED-1 downto 0);
        MEM_AVMM_READ          : out std_logic_vector(MEM_PORTS_USED-1 downto 0);
        MEM_AVMM_WRITE         : out std_logic_vector(MEM_PORTS_USED-1 downto 0);
        MEM_AVMM_ADDRESS       : out slv_array_t(MEM_PORTS_USED-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
        MEM_AVMM_BURSTCOUNT    : out slv_array_t(MEM_PORTS_USED-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
        MEM_AVMM_WRITEDATA     : out slv_array_t(MEM_PORTS_USED-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
        MEM_AVMM_READDATA      : in  slv_array_t(MEM_PORTS_USED-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
        MEM_AVMM_READDATAVALID : in  std_logic_vector(MEM_PORTS_USED-1 downto 0)
    );
end entity;

architecture FULL of APP_SUBCORE is

    constant DMA_TX_PER_ETH_CHAN : natural := DMA_TX_CHANNELS/ETH_CHANNELS;

    -- Internal avmm signal width before splitting into multiple streams
    constant INT_DATA_WIDTH : natural := MEM_PORTS_USED*MEM_DATA_WIDTH;

    -- RX header path fifo data width  (header + dma channel number)
    constant ALL_ONES            : std_logic_vector(MEM_PORTS_USED-1 downto 0) := (others => '1');
    constant MAX_OUTSTANDING     : natural := 16;

    constant MI_PORTS_INT : natural := 5;
    constant DBG_PROBES   : natural := 3;

    constant MI_ADDR_BASES : slv_array_t(MI_PORTS_INT-1 downto 0)(MI_ADDR_WIDTH-1 downto 0) :=
        (
            4 => std_logic_vector(to_unsigned(16#4000#, MI_ADDR_WIDTH)),
            3 => std_logic_vector(to_unsigned(16#3000#, MI_ADDR_WIDTH)),
            2 => std_logic_vector(to_unsigned(16#2000#, MI_ADDR_WIDTH)),
            1 => std_logic_vector(to_unsigned(16#1000#, MI_ADDR_WIDTH)),
            0 => std_logic_vector(to_unsigned(16#0000#, MI_ADDR_WIDTH))
        );

    -- Only decode lower 16 bits (subcore-local address space)
    -- Upper bits contain the subcore base address from top-level splitter
    constant MI_ADDR_MASK_C : std_logic_vector(MI_ADDR_WIDTH-1 downto 0) :=
        std_logic_vector(to_unsigned(16#FFFF#, MI_ADDR_WIDTH));

    signal mi_int_dwr  : slv_array_t(MI_PORTS_INT-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_int_addr : slv_array_t(MI_PORTS_INT-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal mi_int_be   : slv_array_t(MI_PORTS_INT-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal mi_int_rd   : std_logic_vector(MI_PORTS_INT-1 downto 0);
    signal mi_int_wr   : std_logic_vector(MI_PORTS_INT-1 downto 0);
    signal mi_int_ardy : std_logic_vector(MI_PORTS_INT-1 downto 0);
    signal mi_int_drd  : slv_array_t(MI_PORTS_INT-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_int_drdy : std_logic_vector(MI_PORTS_INT-1 downto 0);

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


    -- AXI-Stream between MFB2AXI and DRAM_FIFO
    signal dram_rx_axi_data        : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dram_rx_axi_keep        : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH/8-1 downto 0);
    signal dram_rx_axi_last        : std_logic;
    signal dram_rx_axi_valid       : std_logic;
    signal dram_rx_axi_ready       : std_logic;

    -- AXI-Stream between DRAM_FIFO and AXI2MFB
    signal dram_tx_axi_data      : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dram_tx_axi_keep      : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH/8-1 downto 0);
    signal dram_tx_axi_last      : std_logic;
    signal dram_tx_axi_valid     : std_logic;
    signal dram_tx_axi_ready     : std_logic;
    signal dram_tx_axi_ready_raw : std_logic; -- unmasked readiness reported by AXI2MFB
    signal dram_tx_pkt_len       : std_logic_vector(log2(USR_PKT_SIZE_MAX+1)-1 downto 0);

    -- Drain-side channel router signals
    signal drain_router_chan     : std_logic_vector(MFB_REGIONS*log2(DMA_RX_CHANNELS)-1 downto 0);
    signal drain_router_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal drain_router_src_rdy  : std_logic;
    signal drain_router_dst_rdy  : std_logic;

    -- Drain-side channel router outputs (registered, drive DMA_RX_MVB directly)
    signal drain_router_tx_len     : std_logic_vector(MFB_REGIONS*log2(USR_PKT_SIZE_MAX+1)-1 downto 0);
    signal drain_router_tx_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal drain_router_tx_src_rdy : std_logic;
    signal drain_router_tx_dst_rdy : std_logic;

    -- Track first payload beat for MVB synchronization
    signal drain_first_beat        : std_logic;

    -- AVMM internal signals
    -- between DRAM_FIFO and split
    signal int_avmm_address       : std_logic_vector(MEM_ADDR_WIDTH-1 downto 0);
    signal int_avmm_burstcount    : std_logic_vector(MEM_BURST_WIDTH-1 downto 0);
    signal int_avmm_write         : std_logic;
    signal int_avmm_writedata     : std_logic_vector(INT_DATA_WIDTH-1 downto 0);
    signal int_avmm_read          : std_logic;
    signal int_avmm_ready         : std_logic;
    signal int_avmm_readdata      : std_logic_vector(INT_DATA_WIDTH-1 downto 0);
    signal int_avmm_readdatavalid : std_logic;

    signal mi_m_ardy     : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal accepted      : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal mi_m_drdy     : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal mi_m_drd      : slv_array_t(MEM_PORTS_USED-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mi_m_drdy_reg : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal mi_m_wr       : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal mi_m_rd       : std_logic_vector(MEM_PORTS_USED-1 downto 0);

    signal read_fifo_empty      : std_logic_vector(MEM_PORTS_USED-1 downto 0);
    signal outstanding_read_cnt : unsigned(log2(MAX_OUTSTANDING) downto 0);
    signal read_allowed         : std_logic;

    signal dbg_block   : std_logic_vector(DBG_PROBES-1 downto 0);
    signal dbg_drop    : std_logic_vector(DBG_PROBES-1 downto 0);
    signal dbg_src_rdy : std_logic_vector(DBG_PROBES-1 downto 0);
    signal dbg_dst_rdy : std_logic_vector(DBG_PROBES-1 downto 0);
    signal dbg_sof     : std_logic_vector(DBG_PROBES*MFB_REGIONS-1 downto 0);
    signal dbg_eof     : std_logic_vector(DBG_PROBES*MFB_REGIONS-1 downto 0);

    signal ethdbg_rx_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethdbg_rx_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ethdbg_rx_mfb_src_rdy : std_logic;
    signal ethdbg_rx_mfb_dst_rdy : std_logic;

    signal dram_tx_mfb_src_rdy   : std_logic;
    signal dram_tx_mfb_dst_rdy   : std_logic;
    signal dram_tx_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dram_tx_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal dmadbg_tx_mfb_src_rdy   : std_logic;
    signal dmadbg_tx_mfb_dst_rdy   : std_logic;
    signal dmadbg_tx_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal dmadbg_tx_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal dram_full                : std_logic;
    signal capture_enable           : std_logic := '0';
    signal read_enable              : std_logic := '0';

    -- MFB_DISCARDER output signals (gated RX path)
    signal disc_rx_mvb_data    : std_logic_vector(MFB_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal disc_rx_mvb_vld     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal disc_rx_mvb_src_rdy : std_logic;
    signal disc_rx_mvb_dst_rdy : std_logic;

    signal disc_rx_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal disc_rx_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal disc_rx_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal disc_rx_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal disc_rx_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal disc_rx_mfb_src_rdy : std_logic;
    signal disc_rx_mfb_dst_rdy : std_logic;

begin
    assert (ETH_CHANNELS = 1)
        report "APP_SUBCORE: DRAM packet capture supports only one ETH channel per stream (n6010, 100g2)."
        severity failure;

    -- =========================================================================
    --  MI SPLITTER FOR INTERNAL COMPONENTS
    -- =========================================================================
    -- Routes MI transactions to internal components based on address:
    --   0x0000-0x0FFF : channel router (port 0)
    --   0x1000-0x1FFF : RX speed meter (port 1)
    --   0x2000-0x2FFF : TX speed meter (port 2)
    mi_splitter_int_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH => MI_ADDR_WIDTH,
        DATA_WIDTH => MI_DATA_WIDTH,
        META_WIDTH => 0,
        PORTS      => MI_PORTS_INT,
        ADDR_BASE  => MI_ADDR_BASES,
        ADDR_MASK  => MI_ADDR_MASK_C,
        DEVICE     => DEVICE
    )
    port map (
        CLK     => CLK,
        RESET   => RESET,

        RX_DWR  => MI_DWR,
        RX_MWR  => (others => '0'),
        RX_ADDR => MI_ADDR,
        RX_BE   => MI_BE,
        RX_RD   => MI_RD,
        RX_WR   => MI_WR,
        RX_ARDY => MI_ARDY,
        RX_DRD  => MI_DRD,
        RX_DRDY => MI_DRDY,

        TX_DWR  => mi_int_dwr,
        TX_MWR  => open,
        TX_ADDR => mi_int_addr,
        TX_BE   => mi_int_be,
        TX_RD   => mi_int_rd,
        TX_WR   => mi_int_wr,
        TX_ARDY => mi_int_ardy,
        TX_DRD  => mi_int_drd,
        TX_DRDY => mi_int_drdy
    );

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
        dma_tx_mvb_ethch2_arr(i)                     <= resize(unsigned(dma_tx_mvb_ethch_arr(i)),ETH_TX_HDR_PORT_W) + (SUBCORE_ID*ETH_CHANNELS);
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_PORT)      <= std_logic_vector(dma_tx_mvb_ethch2_arr(i));
        -- Packet length in bytes
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_LENGTH)    <= std_logic_vector(resize(unsigned(dma_tx_mvb_len_arr(i)),ETH_TX_HDR_LENGTH_W));
        -- The discard feature is not currently supported in TX MAX Lite.
        dma_tx_mvb_data_arr(i)(ETH_TX_HDR_DISCARD_O) <= '0';
    end generate;

    dbg_tx_in_i : entity work.STREAMING_DEBUG_PROBE_MFB
    generic map (
        REGIONS       => MFB_REGIONS
    )
    port map (
        RX_SRC_RDY    => DMA_TX_MFB_SRC_RDY,
        RX_DST_RDY    => DMA_TX_MFB_DST_RDY,
        RX_SOF        => DMA_TX_MFB_SOF,
        RX_EOF        => DMA_TX_MFB_EOF,

        TX_SRC_RDY    => dmadbg_tx_mfb_src_rdy,
        TX_DST_RDY    => dmadbg_tx_mfb_dst_rdy,
        TX_SOF        => dmadbg_tx_mfb_sof,
        TX_EOF        => dmadbg_tx_mfb_eof,

        DEBUG_BLOCK   => dbg_block(2),
        DEBUG_DROP    => dbg_drop(2),
        DEBUG_SRC_RDY => dbg_src_rdy(2),
        DEBUG_DST_RDY => dbg_dst_rdy(2),
        DEBUG_SOF     => dbg_sof(2*MFB_REGIONS+MFB_REGIONS-1 downto 2*MFB_REGIONS),
        DEBUG_EOF     => dbg_eof(2*MFB_REGIONS+MFB_REGIONS-1 downto 2*MFB_REGIONS)
    );

    tx_mvb_ins_i : entity work.METADATA_INSERTOR
    generic map (
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
    port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_MVB_DATA     => slv_array_ser(dma_tx_mvb_data_arr),
        RX_MVB_VLD      => DMA_TX_MVB_VLD,
        RX_MVB_SRC_RDY  => DMA_TX_MVB_SRC_RDY,
        RX_MVB_DST_RDY  => DMA_TX_MVB_DST_RDY,

        RX_MFB_DATA     => DMA_TX_MFB_DATA,
        RX_MFB_SOF      => dmadbg_tx_mfb_sof,
        RX_MFB_EOF      => dmadbg_tx_mfb_eof,
        RX_MFB_SOF_POS  => DMA_TX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => DMA_TX_MFB_EOF_POS,
        RX_MFB_SRC_RDY  => dmadbg_tx_mfb_src_rdy,
        RX_MFB_DST_RDY  => dmadbg_tx_mfb_dst_rdy,

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
    generic map (
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REG_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,
        META_WIDTH  => ETH_TX_HDR_WIDTH,
        FAKE_PIPE   => false,
        USE_DST_RDY => true,
        DEVICE      => DEVICE
    )
    port map (
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
    -- PACKET DISCARDER
    -- ------------------------------------
    -- Discards entire packets when capture_enable = '0'
    mfb_discarder_i : entity work.MFB_DISCARDER
    generic map (
        REGIONS          => MFB_REGIONS,
        MVB_ITEM_WIDTH   => ETH_RX_HDR_WIDTH,
        MFB_REG_SIZE     => MFB_REG_SIZE,
        MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
        OUTPUT_FIFO_SIZE => 32,
        DEVICE           => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        -- MVB input (from ETH)
        RX_MVB_DATA    => ETH_RX_MVB_DATA,
        RX_MVB_DISCARD => (others => not capture_enable),
        RX_MVB_VLD     => ETH_RX_MVB_VLD,
        RX_MVB_SRC_RDY => ETH_RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => ETH_RX_MVB_DST_RDY,

        -- MFB input (directly from ETH, before debug probe)
        RX_MFB_DATA    => ETH_RX_MFB_DATA,
        RX_MFB_SOF     => ETH_RX_MFB_SOF,
        RX_MFB_EOF     => ETH_RX_MFB_EOF,
        RX_MFB_SOF_POS => ETH_RX_MFB_SOF_POS,
        RX_MFB_EOF_POS => ETH_RX_MFB_EOF_POS,
        RX_MFB_SRC_RDY => ETH_RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY => ETH_RX_MFB_DST_RDY,

        -- MVB output (to channel router)
        TX_MVB_DATA    => disc_rx_mvb_data,
        TX_MVB_VLD     => disc_rx_mvb_vld,
        TX_MVB_SRC_RDY => disc_rx_mvb_src_rdy,
        TX_MVB_DST_RDY => disc_rx_mvb_dst_rdy,

        -- MFB output (to MFB2AXI)
        TX_MFB_DATA    => disc_rx_mfb_data,
        TX_MFB_SOF     => disc_rx_mfb_sof,
        TX_MFB_EOF     => disc_rx_mfb_eof,
        TX_MFB_SOF_POS => disc_rx_mfb_sof_pos,
        TX_MFB_EOF_POS => disc_rx_mfb_eof_pos,
        TX_MFB_SRC_RDY => disc_rx_mfb_src_rdy,
        TX_MFB_DST_RDY => disc_rx_mfb_dst_rdy
    );

    -- Reads from mvb fifo in discarder, thus discarding the MVB headers
    disc_rx_mvb_dst_rdy <= '1';

    -- ------------------------------------
    -- RX DATA PATH
    -- ------------------------------------

    rx_speed_meter_i : entity work.MFB_SPEED_METER_MI
    generic map (
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REG_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,

        CNT_TICKS_WIDTH  => 24,
        CNT_BYTES_WIDTH  => 32,
        COUNT_PACKETS    => true,
        ADD_ARR_PKTS     => false,
        FREQUENCY        => 200,
        MI_DATA_WIDTH    => MI_DATA_WIDTH,
        MI_ADDRESS_WIDTH => MI_ADDR_WIDTH
    )
    port map (
        CLK => CLK,
        RST => RESET,

        MI_DWR  => mi_int_dwr(1),
        MI_ADDR => mi_int_addr(1),
        MI_BE   => mi_int_be(1),
        MI_RD   => mi_int_rd(1),
        MI_WR   => mi_int_wr(1),
        MI_ARDY => mi_int_ardy(1),
        MI_DRD  => mi_int_drd(1),
        MI_DRDY => mi_int_drdy(1),

        RX_SOF_POS => ETH_RX_MFB_SOF_POS,
        RX_EOF_POS => ETH_RX_MFB_EOF_POS,
        RX_SOF     => ETH_RX_MFB_SOF,
        RX_EOF     => ETH_RX_MFB_EOF,
        RX_SRC_RDY => ETH_RX_MFB_SRC_RDY,
        RX_DST_RDY => ETH_RX_MFB_DST_RDY
    );

    dbg_rx_in_i : entity work.STREAMING_DEBUG_PROBE_MFB
    generic map (
        REGIONS       => MFB_REGIONS
    )
    port map (
        RX_SRC_RDY    => disc_rx_mfb_src_rdy,
        RX_DST_RDY    => disc_rx_mfb_dst_rdy,
        RX_SOF        => disc_rx_mfb_sof,
        RX_EOF        => disc_rx_mfb_eof,

        TX_SRC_RDY    => ethdbg_rx_mfb_src_rdy,
        TX_DST_RDY    => ethdbg_rx_mfb_dst_rdy,
        TX_SOF        => ethdbg_rx_mfb_sof,
        TX_EOF        => ethdbg_rx_mfb_eof,

        DEBUG_BLOCK   => dbg_block(0),
        DEBUG_DROP    => dbg_drop(0),
        DEBUG_SRC_RDY => dbg_src_rdy(0),
        DEBUG_DST_RDY => dbg_dst_rdy(0),
        DEBUG_SOF     => dbg_sof(0*MFB_REGIONS+MFB_REGIONS-1 downto 0*MFB_REGIONS),
        DEBUG_EOF     => dbg_eof(0*MFB_REGIONS+MFB_REGIONS-1 downto 0*MFB_REGIONS)
    );

    mfb2axi_i : entity work.MFB2AXI
    generic map (
        USE_IN_PIPE     => True,
        USE_OUT_PIPE    => True,
        REGIONS         => MFB_REGIONS,
        REGION_SIZE     => MFB_REG_SIZE,
        BLOCK_SIZE      => MFB_BLOCK_SIZE,
        ITEM_WIDTH      => MFB_ITEM_WIDTH,

        AXI_DATA_WIDTH  => MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,

        PIPE_TYPE       => "SHREG",
        DEVICE          => DEVICE
    )
    port map (
        CLK             => CLK,
        RST             => RESET,

        RX_MFB_DATA     => disc_rx_mfb_data,
        RX_MFB_SOF_POS  => disc_rx_mfb_sof_pos,
        RX_MFB_EOF_POS  => disc_rx_mfb_eof_pos,
        RX_MFB_SOF      => ethdbg_rx_mfb_sof,
        RX_MFB_EOF      => ethdbg_rx_mfb_eof,
        RX_MFB_SRC_RDY  => ethdbg_rx_mfb_src_rdy,
        RX_MFB_DST_RDY  => ethdbg_rx_mfb_dst_rdy,

        TX_AXI_TDATA    => dram_rx_axi_data,
        TX_AXI_TKEEP    => dram_rx_axi_keep,
        TX_AXI_TLAST    => dram_rx_axi_last,
        TX_AXI_TVALID   => dram_rx_axi_valid,
        TX_AXI_TREADY   => dram_rx_axi_ready
    );

    dram_fifo_i : entity work.DRAM_FIFO
    generic map (
        AXI_DATA_WIDTH      => MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,
        FIFO_ITEMS          => 2 ** RING_ADDR_WIDTH,
        PKT_MTU             => USR_PKT_SIZE_MAX,
        DDR_ADDR_WIDTH      => MEM_ADDR_WIDTH,
        DDR_BURST_WIDTH     => MEM_BURST_WIDTH,
        DDR_DATA_WIDTH      => INT_DATA_WIDTH,      -- 512b
        DEVICE              => DEVICE,
        FIFO_BUFF_IN_ITEMS  => 2**16,
        FIFO_BUFF_OUT_ITEMS => 2**12
    )
    port map (
        CLK                 => CLK,
        RESET               => RESET,

        RX_AXI_DATA  => dram_rx_axi_data,
        RX_AXI_KEEP  => dram_rx_axi_keep,
        RX_AXI_LAST  => dram_rx_axi_last,
        RX_AXI_VALID => dram_rx_axi_valid,
        RX_AXI_READY => dram_rx_axi_ready,

        TX_AXI_DATA  => dram_tx_axi_data,
        TX_AXI_KEEP  => dram_tx_axi_keep,
        TX_AXI_LAST  => dram_tx_axi_last,
        TX_AXI_VALID => dram_tx_axi_valid,
        TX_AXI_READY => dram_tx_axi_ready,

        TX_PKT_LEN   => dram_tx_pkt_len,

        AVMM_ADDRESS       => int_avmm_address,
        AVMM_BURSTCOUNT    => int_avmm_burstcount,
        AVMM_WRITE         => int_avmm_write,
        AVMM_WRITEDATA     => int_avmm_writedata,
        AVMM_READ          => int_avmm_read,
        AVMM_READY         => int_avmm_ready,
        AVMM_READDATA      => int_avmm_readdata,
        AVMM_READDATAVALID => int_avmm_readdatavalid,

        DDR_FULL           => dram_full,
        DDR_READ_EN        => read_enable

    );

    axi2mfb_i : entity work.AXI2MFB
    generic map (
        USE_IN_PIPE     => True,
        USE_OUT_PIPE    => True,
        REGIONS         => MFB_REGIONS,
        REGION_SIZE     => MFB_REG_SIZE,
        BLOCK_SIZE      => MFB_BLOCK_SIZE,
        ITEM_WIDTH      => MFB_ITEM_WIDTH,

        AXI_DATA_WIDTH  => MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH,

        PIPE_TYPE       => "SHREG",
        DEVICE          => DEVICE
    )
    port map (
        CLK             => CLK,
        RST             => RESET,

        RX_AXI_TDATA    => dram_tx_axi_data,
        RX_AXI_TKEEP    => dram_tx_axi_keep,
        RX_AXI_TLAST    => dram_tx_axi_last,
        RX_AXI_TVALID   => dram_tx_axi_valid and (not drain_first_beat or drain_router_dst_rdy),
        RX_AXI_TREADY   => dram_tx_axi_ready_raw,

        TX_MFB_DATA     => DMA_RX_MFB_DATA,
        TX_MFB_META     => open,
        TX_MFB_SOF_POS  => DMA_RX_MFB_SOF_POS,
        TX_MFB_EOF_POS  => DMA_RX_MFB_EOF_POS,
        TX_MFB_SOF      => dram_tx_mfb_sof,
        TX_MFB_EOF      => dram_tx_mfb_eof,
        TX_MFB_SRC_RDY  => dram_tx_mfb_src_rdy,
        TX_MFB_DST_RDY  => dram_tx_mfb_dst_rdy
    );

    dbg_rx_out_i : entity work.STREAMING_DEBUG_PROBE_MFB
    generic map (
        REGIONS => MFB_REGIONS
    )
    port map (
        RX_SRC_RDY => dram_tx_mfb_src_rdy,
        RX_DST_RDY => dram_tx_mfb_dst_rdy,
        RX_SOF     => dram_tx_mfb_sof,
        RX_EOF     => dram_tx_mfb_eof,

        TX_SRC_RDY => DMA_RX_MFB_SRC_RDY,
        TX_DST_RDY => DMA_RX_MFB_DST_RDY,
        TX_SOF     => DMA_RX_MFB_SOF,
        TX_EOF     => DMA_RX_MFB_EOF,

        DEBUG_BLOCK   => '0',
        DEBUG_DROP    => '0',
        DEBUG_SRC_RDY => dbg_src_rdy(1),
        DEBUG_DST_RDY => dbg_dst_rdy(1),
        DEBUG_SOF     => dbg_sof(1*MFB_REGIONS+MFB_REGIONS-1 downto 1*MFB_REGIONS),
        DEBUG_EOF     => dbg_eof(1*MFB_REGIONS+MFB_REGIONS-1 downto 1*MFB_REGIONS)
    );

    tx_speed_meter_i : entity work.MFB_SPEED_METER_MI
    generic map (
        REGIONS     => MFB_REGIONS,
        REGION_SIZE => MFB_REG_SIZE,
        BLOCK_SIZE  => MFB_BLOCK_SIZE,
        ITEM_WIDTH  => MFB_ITEM_WIDTH,

        CNT_TICKS_WIDTH  => 24,
        CNT_BYTES_WIDTH  => 32,
        COUNT_PACKETS    => true,
        ADD_ARR_PKTS     => false,
        FREQUENCY        => 200,
        MI_DATA_WIDTH    => MI_DATA_WIDTH,
        MI_ADDRESS_WIDTH => MI_ADDR_WIDTH
    )
    port map (
        CLK => CLK,
        RST => RESET,

        MI_DWR  => mi_int_dwr(2),
        MI_ADDR => mi_int_addr(2),
        MI_BE   => mi_int_be(2),
        MI_RD   => mi_int_rd(2),
        MI_WR   => mi_int_wr(2),
        MI_ARDY => mi_int_ardy(2),
        MI_DRD  => mi_int_drd(2),
        MI_DRDY => mi_int_drdy(2),

        RX_SOF_POS => DMA_RX_MFB_SOF_POS,
        RX_EOF_POS => DMA_RX_MFB_EOF_POS,
        RX_SOF     => DMA_RX_MFB_SOF,
        RX_EOF     => DMA_RX_MFB_EOF,
        RX_SRC_RDY => DMA_RX_MFB_SRC_RDY,
        RX_DST_RDY => DMA_RX_MFB_DST_RDY
    );

    -- ------------------------------------
    -- RX HEADER PATH
    -- ------------------------------------
    -- Read pkt_len from DRAM_FIFO and recreate MVB signals

    -- Route packets from ETH channel to DMA channels
    drain_chan_router_i : entity work.MVB_CHANNEL_ROUTER_MI
    generic map (
        ITEMS        => MFB_REGIONS,
        ITEM_WIDTH   => log2(USR_PKT_SIZE_MAX+1),
        SRC_CHANNELS => ETH_CHANNELS,
        DST_CHANNELS => DMA_RX_CHANNELS,
        DEFAULT_MODE => 2,                  -- round-robin across all DMA channels
        OPT_MODE     => True,
        DEVICE       => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        MI_DWR     => mi_int_dwr(0),
        MI_ADDR    => mi_int_addr(0),
        MI_BE      => mi_int_be(0),
        MI_RD      => mi_int_rd(0),
        MI_WR      => mi_int_wr(0),
        MI_ARDY    => mi_int_ardy(0),
        MI_DRD     => mi_int_drd(0),
        MI_DRDY    => mi_int_drdy(0),

        RX_DATA    => dram_tx_pkt_len,
        RX_CHANNEL => (others => '0'),  -- hardwired to channel 0
        RX_VLD     => drain_router_vld,
        RX_SRC_RDY => drain_router_src_rdy,
        RX_DST_RDY => drain_router_dst_rdy,

        TX_DATA    => drain_router_tx_len,
        TX_CHANNEL => drain_router_chan,
        TX_VLD     => drain_router_tx_vld,
        TX_SRC_RDY => drain_router_tx_src_rdy,
        TX_DST_RDY => drain_router_tx_dst_rdy
    );

    drain_router_tx_dst_rdy <= DMA_RX_MVB_DST_RDY or not drain_router_tx_src_rdy;
    dram_tx_axi_ready       <= dram_tx_axi_ready_raw and (not drain_first_beat or drain_router_dst_rdy);

    -- Detect first payload beat from DRAM FIFO
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                drain_first_beat <= '1';
            elsif (dram_tx_axi_valid = '1' and dram_tx_axi_ready = '1') then
                if (dram_tx_axi_last = '1') then
                    drain_first_beat <= '1';  -- next beat is first of new packet
                else
                    drain_first_beat <= '0';
                end if;
            end if;
        end if;
    end process;

    -- Present MVB header on first payload beat - TRIGGER channel router.
    drain_router_vld     <= (others => drain_first_beat and dram_tx_axi_valid and dram_tx_axi_ready);
    drain_router_src_rdy <= drain_first_beat and dram_tx_axi_valid and dram_tx_axi_ready;

    -- Connect to DMA_RX_MVB outputs
    DMA_RX_MVB_LEN      <= drain_router_tx_len;
    DMA_RX_MVB_HDR_META <= (others => '0');
    DMA_RX_MVB_CHANNEL  <= drain_router_chan;
    DMA_RX_MVB_DISCARD  <= (others => '0');
    DMA_RX_MVB_VLD      <= drain_router_tx_vld;
    DMA_RX_MVB_SRC_RDY  <= drain_router_tx_src_rdy;

    -- ---------------------------------------------
    -- AVMM port splitting & clock domain crossing
    -- ---------------------------------------------

    -- Both fifos must be ready in order to preserve synchronization
    int_avmm_ready <= '1' when (mi_m_ardy or accepted) = ALL_ONES else '0';

    -- FIFO on each port is NOT empty
    int_avmm_readdatavalid <= and (not read_fifo_empty);

    -- Prevents read_fifo_g overflow
    read_allowed <= '1' when outstanding_read_cnt < MAX_OUTSTANDING else '0';

    gen_mi_m : for p in 0 to MEM_PORTS_USED-1 generate
        mi_m_wr(p) <= int_avmm_write and not accepted(p);
        mi_m_rd(p) <= int_avmm_read and read_allowed and not accepted(p);
    end generate;

    -- Read/write port synchronization
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                accepted <= (others => '0');
            else
                -- capture each ardy signal into a register
                for p in 0 to MEM_PORTS_USED-1 loop
                    if (mi_m_ardy(p) = '1') then
                        accepted(p) <= '1';
                    end if;
                end loop;
                -- when both are set reset them back to 0
                if ((accepted or mi_m_ardy) = ALL_ONES) then
                    accepted <= (others => '0');
                end if;
            end if;
        end if;
    end process;

    -- Used for clock domain crossing on each port
    cdc_avmm_g : for p in 0 to MEM_PORTS_USED-1 generate
        asfifo_in_i : entity work.MI_ASYNC
        generic map (
            DATA_WIDTH  => MEM_DATA_WIDTH,
            ADDR_WIDTH  => MEM_ADDR_WIDTH,
            META_WIDTH  => MEM_BURST_WIDTH, -- in case bursts are used in the future
            RAM_TYPE    => "BRAM",
            RESET_LOGIC => true,
            DEVICE      => DEVICE
        )
        port map (
            -- Master interface
            CLK_M       => CLK,
            RESET_M     => RESET,

            MI_M_ADDR   => int_avmm_address,

            MI_M_DWR    => int_avmm_writedata((p+1)*MEM_DATA_WIDTH-1 downto p*MEM_DATA_WIDTH),
            MI_M_MWR    => int_avmm_burstcount,
            MI_M_WR     => mi_m_wr(p),
            MI_M_BE     => (others => '1'),

            MI_M_DRD    => mi_m_drd(p),
            MI_M_RD     => mi_m_rd(p),
            MI_M_DRDY   => mi_m_drdy(p),

            MI_M_ARDY   => mi_m_ardy(p),        -- request was accepted

            -- Slave interface
            CLK_S       => MEM_CLK(p),
            RESET_S     => MEM_RST(p),

            MI_S_ADDR   => MEM_AVMM_ADDRESS(p),

            MI_S_DWR    => MEM_AVMM_WRITEDATA(p),
            MI_S_MWR    => MEM_AVMM_BURSTCOUNT(p),
            MI_S_WR     => MEM_AVMM_WRITE(p),
            MI_S_BE     => open,

            MI_S_DRD    => MEM_AVMM_READDATA(p),
            MI_S_RD     => MEM_AVMM_READ(p),
            MI_S_DRDY   => MEM_AVMM_READDATAVALID(p),

            MI_S_ARDY   => MEM_AVMM_READY(p)

        );
    end generate;

    read_fifo_g : for p in 0 to MEM_PORTS_USED-1 generate
        read_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => MEM_DATA_WIDTH,
            ITEMS               => MAX_OUTSTANDING,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 1,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => false
        )
        port map (
            CLK    => CLK,
            RESET  => RESET,

            -- Write interface
            DI     => mi_m_drd(p),
            WR     => mi_m_drdy(p),
            FULL   => open,
            AFULL  => open,
            STATUS => open,

            -- Read interface
            DO     => int_avmm_readdata((p+1)*MEM_DATA_WIDTH-1 downto p*MEM_DATA_WIDTH),
            RD     => int_avmm_readdatavalid,
            EMPTY  => read_fifo_empty(p),
            AEMPTY => open
        );
    end generate;

    -- Outstanding reads counter
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                outstanding_read_cnt <= (others => '0');
            else
                if (int_avmm_ready = '1' and int_avmm_read = '1' and int_avmm_readdatavalid = '0') then
                    outstanding_read_cnt <= outstanding_read_cnt + 1;
                elsif (int_avmm_readdatavalid = '1' and not (int_avmm_ready = '1' and int_avmm_read = '1')) then
                    outstanding_read_cnt <= outstanding_read_cnt - 1;
                end if;
            end if;
        end if;
    end process;

    -- ---------------------------------------------
    -- Debug probes
    -- ---------------------------------------------
    dbg_master_i : entity work.STREAMING_DEBUG_MASTER
    generic map (
        CONNECTED_PROBES => DBG_PROBES,
        REGIONS          => MFB_REGIONS,
        DEBUG_ENABLED    => true,
        PROBE_ENABLED    => "EEE",
        COUNTER_WORD     => "EEE",
        COUNTER_WAIT     => "EEE",
        COUNTER_DST_HOLD => "EEE",
        COUNTER_SRC_HOLD => "EEE",
        COUNTER_SOP      => "EEE",
        COUNTER_EOP      => "EEE",
        BUS_CONTROL      => "DDD",
        PROBE_NAMES      => "RxInRxOtTxIn",
        DEBUG_REG        => false
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        MI_DWR  => mi_int_dwr(3),
        MI_ADDR => mi_int_addr(3),
        MI_RD   => mi_int_rd(3),
        MI_WR   => mi_int_wr(3),
        MI_BE   => mi_int_be(3),
        MI_DRD  => mi_int_drd(3),
        MI_ARDY => mi_int_ardy(3),
        MI_DRDY => mi_int_drdy(3),

        DEBUG_BLOCK   => dbg_block,
        DEBUG_DROP    => dbg_drop,
        DEBUG_SRC_RDY => dbg_src_rdy,
        DEBUG_DST_RDY => dbg_dst_rdy,
        DEBUG_SOP     => dbg_sof,
        DEBUG_EOP     => dbg_eof
    );

    -- ---------------------------------------------
    -- Status & control registers
    -- ---------------------------------------------

    status_rd_p : process (CLK)
    begin
        if rising_edge(CLK) then
            case mi_int_addr(4)(4 downto 0) is
                when "00000" =>
                    mi_int_drd(4) <= (0 => dram_full, others => '0');

                when "00100" =>
                    mi_int_drd(4) <= (0 => capture_enable, others => '0');

                when "01000" =>
                    mi_int_drd(4) <= (0 => read_enable, others => '0');

                when others =>
                    mi_int_drd(4) <= (others => '0');
            end case;
        end if;
    end process;

    status_wr_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (mi_int_wr(4) = '1' and mi_int_addr(4)(4 downto 0) = "00100") then
                capture_enable <= mi_int_dwr(4)(0);
            elsif (mi_int_wr(4) = '1' and mi_int_addr(4)(4 downto 0) = "01000") then
                read_enable <= mi_int_dwr(4)(0);
            end if;

            -- Disable capture when DDR is full
            if (dram_full = '1') then
                capture_enable <= '0';
            end if;

            if (RESET = '1') then
                capture_enable <= '0';
                read_enable    <= '0';
            end if;
        end if;
    end process;

    -- Set MI response control signals
    mi_int_ardy(4) <= mi_int_rd(4) or mi_int_wr(4);

    drdy_p : process (CLK)
    begin
        if rising_edge(CLK) then
            mi_int_drdy(4) <= mi_int_rd(4);
            if (RESET = '1') then
                mi_int_drdy(4) <= '0';
            end if;
        end if;
    end process;

end architecture;
