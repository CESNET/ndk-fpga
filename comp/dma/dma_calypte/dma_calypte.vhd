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
    generic(
        -- ==========================================================================================
        -- Global settings
        --
        -- Settings affecting both RX and TX or the top level entity itself
        -- ==========================================================================================
        -- Name of target device, the supported are:
        -- "ULTRASCALE"
        DEVICE : string := "ULTRASCALE";

        -- USER MFB data bus configuration
        -- Defines the total width of User data stream.
        USR_MFB_REGIONS     : natural := 1;
        USR_MFB_REGION_SIZE : natural := 8;
        USR_MFB_BLOCK_SIZE  : natural := 8;
        USR_MFB_ITEM_WIDTH  : natural := 8;

        -- ==========================================================================================
        -- PCIe-side bus settings
        -- ==========================================================================================
        -- Requester Request MFB interface configration, allowed configurations are:
        -- (1,1,8,32)
        PCIE_RQ_MFB_REGIONS     : natural := 2;
        PCIE_RQ_MFB_REGION_SIZE : natural := 1;
        PCIE_RQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RQ_MFB_ITEM_WIDTH  : natural := 32;

        -- Completer Request MFB interface configration, allowed configurations are:
        -- (1,1,8,32)
        PCIE_CQ_MFB_REGIONS     : natural := 2;
        PCIE_CQ_MFB_REGION_SIZE : natural := 1;
        PCIE_CQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CQ_MFB_ITEM_WIDTH  : natural := 32;

        -- Width of User Header Metadata information
        -- on RX: added to header sent to header Buffer in RAM
        -- on TX: extracted from descriptor and propagated to output
        HDR_META_WIDTH : natural := 24;

        -- ==========================================================================================
        -- RX DMA settings
        --
        -- Settings for RX direction of DMA Module
        -- ==========================================================================================
        -- Total number of RX DMA Channels (multiples of 2 at best)
        -- Minimum: 4
        RX_CHANNELS         : natural := 8;
        -- Width of Software and Hardware Descriptor Pointer
        -- Defines width of signals used for these values in DMA Module
        -- Affects logic complexity
        -- Maximum value: 32 (restricted by size of SDP and HDP MI register)
        RX_PTR_WIDTH        : natural := 16;
        -- Maximum size of a User packet (in bytes)
        -- Defines width of Packet length signals.
        -- the maximum is 2**16 - 1
        USR_RX_PKT_SIZE_MAX : natural := 2**12;
        -- Enables an additional register of the transaction buffer that improves
        -- throughput
        TRBUF_REG_EN        : boolean := false;

        -- =====================================================================
        -- TX DMA settings
        --
        -- Settings for TX direction of DMA Module
        -- =====================================================================
        -- Total number of TX DMA Channels
        -- Minimum value: TX_SEL_CHANNELS*DMA_ENDPOINTS
        TX_CHANNELS         : natural := 8;
        -- Width of Software and Hardware Descriptor Pointer
        -- Defines width of signals used for these values in DMA Module
        -- Affects logic complexity
        -- Maximum value: 32 (restricted by size of SDP and HDP MI register)
        TX_PTR_WIDTH        : natural := 14;
        -- Maximum size of a User packet (in bytes)
        -- Defines width of Packet length signals.
        -- the maximum is 2**16 - 1
        USR_TX_PKT_SIZE_MAX : natural := 2**12;

        -- =====================================================================
        -- Optional settings
        --
        -- Settings for testing and debugging, settings usually left unchanged
        -- at entity-area constants.
        -- =====================================================================
        -- Width of DSP packet and byte statistics counters
        DSP_CNT_WIDTH      : natural := 64;
        -- Enable generation of RX/TX side of DMA Module
        RX_GEN_EN          : boolean := TRUE;
        TX_GEN_EN          : boolean := TRUE;
        ST_SP_DBG_SIGNAL_W : natural := 2;
        -- Width of MI bus
        MI_WIDTH           : natural := 32
        );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =====================================================================
        -- RX DMA User-side MFB
        -- =====================================================================
        USR_RX_MFB_META_CHAN     : in std_logic_vector(log2(RX_CHANNELS) -1 downto 0);
        USR_RX_MFB_META_HDR_META : in std_logic_vector(HDR_META_WIDTH -1 downto 0);

        USR_RX_MFB_DATA    : in  std_logic_vector(USR_MFB_REGIONS*USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE*USR_MFB_ITEM_WIDTH-1 downto 0);
        USR_RX_MFB_SOF     : in  std_logic_vector(USR_MFB_REGIONS -1 downto 0);
        USR_RX_MFB_EOF     : in  std_logic_vector(USR_MFB_REGIONS -1 downto 0);
        USR_RX_MFB_SOF_POS : in  std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE)) -1 downto 0);
        USR_RX_MFB_EOF_POS : in  std_logic_vector(USR_MFB_REGIONS*max(1, log2(USR_MFB_REGION_SIZE*USR_MFB_BLOCK_SIZE)) -1 downto 0);
        USR_RX_MFB_SRC_RDY : in  std_logic;
        USR_RX_MFB_DST_RDY : out std_logic := '1';

        -- =====================================================================
        -- TX DMA User-side MFB
        -- =====================================================================
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

        ST_SP_DBG_CHAN : out std_logic_vector(log2(TX_CHANNELS) -1 downto 0);
        ST_SP_DBG_META : out std_logic_vector(ST_SP_DBG_SIGNAL_W -1 downto 0);

        -- =====================================================================
        -- PCIe-side interfaces
        -- =====================================================================
        -- Upstream MFB interface (for sending data to PCIe Endpoints)
        PCIE_RQ_MFB_DATA    : out std_logic_vector(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_RQ_MFB_META    : out std_logic_vector(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
        PCIE_RQ_MFB_SOF     : out std_logic_vector(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_EOF     : out std_logic_vector(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_SOF_POS : out std_logic_vector(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_EOF_POS : out std_logic_vector(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_SRC_RDY : out std_logic;
        PCIE_RQ_MFB_DST_RDY : in  std_logic;

        -- Downstream MFB interface (for sending data from PCIe Endpoints)
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

    constant TX_INP_FIFO_EN : boolean := FALSE;

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

    signal inp_fifo_status : std_logic_vector(log2(512) downto 0);

    signal inp_fifo_mfb_data    : std_logic_vector(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal inp_fifo_mfb_meta    : std_logic_vector(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
    signal inp_fifo_mfb_sof     : std_logic_vector(PCIE_CQ_MFB_REGIONS -1 downto 0);
    signal inp_fifo_mfb_eof     : std_logic_vector(PCIE_CQ_MFB_REGIONS -1 downto 0);
    signal inp_fifo_mfb_sof_pos : std_logic_vector(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE)) -1 downto 0);
    signal inp_fifo_mfb_eof_pos : std_logic_vector(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE)) -1 downto 0);
    signal inp_fifo_mfb_src_rdy : std_logic;
    signal inp_fifo_mfb_dst_rdy : std_logic;

    -- attribute mark_debug : string;

    -- attribute mark_debug of USR_RX_MFB_META_PKT_SIZE : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_META_CHAN     : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_META_HDR_META : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_DATA          : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SOF_POS       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_EOF_POS       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SOF           : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_EOF           : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_SRC_RDY       : signal is "true";
    -- attribute mark_debug of USR_RX_MFB_DST_RDY       : signal is "true";

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

    -- attribute mark_debug of PCIE_CQ_MFB_DATA    : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_META    : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_SOF     : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_EOF     : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_SOF_POS : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_EOF_POS : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_SRC_RDY : signal is "true";
    -- attribute mark_debug of PCIE_CQ_MFB_DST_RDY : signal is "true";
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
                SW_ADDR_WIDTH  => 64,
                CNTRS_WIDTH    => DSP_CNT_WIDTH,
                HDR_META_WIDTH => HDR_META_WIDTH,
                PKT_SIZE_MAX   => USR_RX_PKT_SIZE_MAX,
                TRBUF_FIFO_EN  => FALSE,
                TRBUF_REG_EN   => TRBUF_REG_EN)

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

                USER_RX_MFB_META_HDR_META => USR_RX_MFB_META_HDR_META,
                USER_RX_MFB_META_CHAN     => USR_RX_MFB_META_CHAN,

                USER_RX_MFB_DATA    => USR_RX_MFB_DATA,
                USER_RX_MFB_SOF     => USR_RX_MFB_SOF,
                USER_RX_MFB_EOF     => USR_RX_MFB_EOF,
                USER_RX_MFB_SOF_POS => USR_RX_MFB_SOF_POS,
                USER_RX_MFB_EOF_POS => USR_RX_MFB_EOF_POS,
                USER_RX_MFB_SRC_RDY => USR_RX_MFB_SRC_RDY,
                USER_RX_MFB_DST_RDY => USR_RX_MFB_DST_RDY,

                PCIE_UP_MFB_DATA    => PCIE_RQ_MFB_DATA,
                PCIE_UP_MFB_META    => PCIE_RQ_MFB_META,
                PCIE_UP_MFB_SOF     => PCIE_RQ_MFB_SOF,
                PCIE_UP_MFB_EOF     => PCIE_RQ_MFB_EOF,
                PCIE_UP_MFB_SOF_POS => PCIE_RQ_MFB_SOF_POS,
                PCIE_UP_MFB_EOF_POS => PCIE_RQ_MFB_EOF_POS,
                PCIE_UP_MFB_SRC_RDY => PCIE_RQ_MFB_SRC_RDY,
                PCIE_UP_MFB_DST_RDY => PCIE_RQ_MFB_DST_RDY);
    else generate
        mi_split_drd(0)  <= x"DEAD_BEAD";
        mi_split_ardy(0) <= mi_split_rd(0) or mi_split_wr(0);
        mi_split_drdy(0) <= mi_split_rd(0);

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

        inp_tx_fifo_g : if (TX_INP_FIFO_EN) generate
            inp_fifo_i : entity work.MFB_FIFOX
                generic map (
                    REGIONS     => PCIE_CQ_MFB_REGIONS,
                    REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
                    BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

                    META_WIDTH          => PCIE_CQ_META_WIDTH,
                    FIFO_DEPTH          => 512,
                    RAM_TYPE            => "AUTO",
                    DEVICE              => DEVICE,
                    ALMOST_FULL_OFFSET  => 2,
                    ALMOST_EMPTY_OFFSET => 2)
                port map (
                    CLK => CLK,
                    RST => RESET,

                    RX_DATA    => PCIE_CQ_MFB_DATA,
                    RX_META    => PCIE_CQ_MFB_META,
                    RX_SOF_POS => PCIE_CQ_MFB_SOF_POS,
                    RX_EOF_POS => PCIE_CQ_MFB_EOF_POS,
                    RX_SOF     => PCIE_CQ_MFB_SOF,
                    RX_EOF     => PCIE_CQ_MFB_EOF,
                    RX_SRC_RDY => PCIE_CQ_MFB_SRC_RDY,
                    RX_DST_RDY => PCIE_CQ_MFB_DST_RDY,

                    TX_DATA    => inp_fifo_mfb_data,
                    TX_META    => inp_fifo_mfb_meta,
                    TX_SOF_POS => inp_fifo_mfb_sof_pos,
                    TX_EOF_POS => inp_fifo_mfb_eof_pos,
                    TX_SOF     => inp_fifo_mfb_sof,
                    TX_EOF     => inp_fifo_mfb_eof,
                    TX_SRC_RDY => inp_fifo_mfb_src_rdy,
                    TX_DST_RDY => inp_fifo_mfb_dst_rdy,

                    FIFO_STATUS => inp_fifo_status,
                    FIFO_AFULL  => open,
                    FIFO_AEMPTY => open);
        else generate
            inp_fifo_mfb_data    <= PCIE_CQ_MFB_DATA;
            inp_fifo_mfb_meta    <= PCIE_CQ_MFB_META;
            inp_fifo_mfb_sof_pos <= PCIE_CQ_MFB_SOF_POS;
            inp_fifo_mfb_eof_pos <= PCIE_CQ_MFB_EOF_POS;
            inp_fifo_mfb_sof     <= PCIE_CQ_MFB_SOF;
            inp_fifo_mfb_eof     <= PCIE_CQ_MFB_EOF;
            inp_fifo_mfb_src_rdy <= PCIE_CQ_MFB_SRC_RDY;
            PCIE_CQ_MFB_DST_RDY  <= inp_fifo_mfb_dst_rdy;
        end generate;

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

                DATA_POINTER_WIDTH    => TX_PTR_WIDTH,
                DMA_HDR_POINTER_WIDTH => TX_PTR_WIDTH-3,
                CHANNELS              => TX_CHANNELS,
                CNTRS_WIDTH           => DSP_CNT_WIDTH,
                HDR_META_WIDTH        => HDR_META_WIDTH,
                ST_SP_DBG_SIGNAL_W    => ST_SP_DBG_SIGNAL_W,
                PKT_SIZE_MAX          => USR_TX_PKT_SIZE_MAX)
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

                PCIE_CQ_MFB_DATA    => inp_fifo_mfb_data,
                PCIE_CQ_MFB_META    => inp_fifo_mfb_meta,
                PCIE_CQ_MFB_SOF     => inp_fifo_mfb_sof,
                PCIE_CQ_MFB_EOF     => inp_fifo_mfb_eof,
                PCIE_CQ_MFB_SOF_POS => inp_fifo_mfb_sof_pos,
                PCIE_CQ_MFB_EOF_POS => inp_fifo_mfb_eof_pos,
                PCIE_CQ_MFB_SRC_RDY => inp_fifo_mfb_src_rdy,
                PCIE_CQ_MFB_DST_RDY => inp_fifo_mfb_dst_rdy,

                ST_SP_DBG_CHAN => ST_SP_DBG_CHAN,
                ST_SP_DBG_META => ST_SP_DBG_META,

                MI_ADDR => mi_split_addr(1),
                MI_DWR  => mi_split_dwr(1),
                MI_BE   => mi_split_be(1),
                MI_RD   => mi_split_rd(1),
                MI_WR   => mi_split_wr(1),
                MI_DRD  => mi_split_drd(1),
                MI_ARDY => mi_split_ardy(1),
                MI_DRDY => mi_split_drdy(1));

    else generate
        mi_split_drd(1) <= x"DEAD_BEAD";
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
    end generate;

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

            DEVICE => DEVICE)
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
            TX_DRDY => mi_split_drdy);
end architecture;
