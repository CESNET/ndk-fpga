-- dma_wrapper.vhd: Wrapper with the DMA Calypte core
-- Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-P-2.0

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.dma_bus_pack.all;
use work.pcie_meta_pack.all;

entity DMA_WRAPPER is
    generic(
        DEVICE : string := "STRATIX10";

        DMA_STREAMS : natural := 1;

        DMA_MFB_REGIONS     : natural := 1;
        DMA_MFB_REGION_SIZE : natural := 8;
        DMA_MFB_BLOCK_SIZE  : natural := 8;
        DMA_MFB_ITEM_WIDTH  : natural := 8;

        PCIE_RQ_MFB_REGIONS     : natural := 2;
        PCIE_RQ_MFB_REGION_SIZE : natural := 1;
        PCIE_RQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RQ_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_RC_MFB_REGIONS     : natural := 2;
        PCIE_RC_MFB_REGION_SIZE : natural := 1;
        PCIE_RC_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RC_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_CQ_MFB_REGIONS     : natural := 2;
        PCIE_CQ_MFB_REGION_SIZE : natural := 1;
        PCIE_CQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CQ_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_CC_MFB_REGIONS     : natural := 2;
        PCIE_CC_MFB_REGION_SIZE : natural := 1;
        PCIE_CC_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CC_MFB_ITEM_WIDTH  : natural := 32;

        HDR_META_WIDTH : natural := 12;
        PKT_SIZE_MAX   : natural := 2**12;

        C2H_CHANNELS  : natural := 8;
        C2H_PTR_WIDTH : natural := 16;

        H2C_CHANNELS  : natural := 8;
        H2C_PTR_WIDTH : natural := 16;

        DSP_CNT_WIDTH : natural := 64;

        C2H_GEN_EN : boolean := TRUE;
        H2C_GEN_EN : boolean := TRUE;

        DMA_DEBUG_ENABLE : boolean := FALSE;

        MI_WIDTH : natural := 32
    );
    port(
        -- =====================================================================
        --  Clock and Reset
        -- =====================================================================
        -- Clock for MI interface
        MI_CLK   : in std_logic;
        MI_RESET : in std_logic;

        -- Clock and reset for the DMA core
        DMA_CLK   : in std_logic_vector(DMA_STREAMS -1 downto 0);
        DMA_RESET : in std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =====================================================================
        --  RX DMA User-side MFB bus
        -- =====================================================================
        C2H_DMA_MFB_META_PKT_SIZE : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1) -1 downto 0);
        C2H_DMA_MFB_META_HDR_META : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
        C2H_DMA_MFB_META_CHAN     : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(C2H_CHANNELS) -1 downto 0);

        C2H_DMA_MFB_DATA    : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto 0);
        C2H_DMA_MFB_SOF     : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        C2H_DMA_MFB_EOF     : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        C2H_DMA_MFB_SOF_POS : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
        C2H_DMA_MFB_EOF_POS : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
        C2H_DMA_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        C2H_DMA_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0) := (others => '1');

        -- =====================================================================
        --  TX DMA User-side MFB bus
        -- =====================================================================
        H2C_DMA_MFB_META_PKT_SIZE : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1) -1 downto 0) := (others => (others => '0'));
        H2C_DMA_MFB_META_HDR_META : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0)       := (others => (others => '0'));
        H2C_DMA_MFB_META_CHAN     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(H2C_CHANNELS) -1 downto 0)   := (others => (others => '0'));

        H2C_DMA_MFB_DATA    : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto 0) := (others => (others => '0'));
        H2C_DMA_MFB_SOF     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0)                                                           := (others => (others => '0'));
        H2C_DMA_MFB_EOF     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0)                                                           := (others => (others => '0'));
        H2C_DMA_MFB_SOF_POS : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0)                         := (others => (others => '0'));
        H2C_DMA_MFB_EOF_POS : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0)      := (others => (others => '0'));
        H2C_DMA_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0)                                                                                   := (others => '0');
        H2C_DMA_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =====================================================================
        --  PCIe-side interfaces
        -- =====================================================================
        -- Upstream MFB interface (for sending data to PCIe Endpoints)
        PCIE_RQ_MFB_DATA    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH -1 downto 0) := (others => (others => '0'));
        PCIE_RQ_MFB_META    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
        PCIE_RQ_MFB_SOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0)                                                                       := (others => (others => '0'));
        PCIE_RQ_MFB_EOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0)                                                                       := (others => (others => '0'));
        PCIE_RQ_MFB_SOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE)) -1 downto 0)                                 := (others => (others => '0'));
        PCIE_RQ_MFB_EOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE)) -1 downto 0)          := (others => (others => '0'));
        PCIE_RQ_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0)                                                                                                    := (others => '0');
        PCIE_RQ_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- Downstream MFB interface (for sending data from PCIe Endpoints)
        PCIE_RC_MFB_DATA    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE*PCIE_RC_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_RC_MFB_SOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS -1 downto 0);
        PCIE_RC_MFB_EOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS -1 downto 0);
        PCIE_RC_MFB_SOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*max(1, log2(PCIE_RC_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_RC_MFB_EOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*max(1, log2(PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RC_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_RC_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0) := (others => '1');

        -- CQ MFB interface (receiving data from PCIe endpoint, DMA Calypte only)
        PCIE_CQ_MFB_DATA    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_CQ_MFB_META    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
        PCIE_CQ_MFB_SOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_EOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_SOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_EOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_CQ_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0) := (others => '0');

        -- CC MFB interface (seinding data to PCIe endpoint, DMA Calypte only)
        PCIE_CC_MFB_DATA    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE*PCIE_CC_MFB_ITEM_WIDTH -1 downto 0) := (others => (others => '0'));
        PCIE_CC_MFB_META    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_META_WIDTH -1 downto 0)                                                    := (others => (others => '0'));
        PCIE_CC_MFB_SOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS -1 downto 0)                                                                       := (others => (others => '0'));
        PCIE_CC_MFB_EOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS -1 downto 0)                                                                       := (others => (others => '0'));
        PCIE_CC_MFB_SOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*max(1, log2(PCIE_CC_MFB_REGION_SIZE)) -1 downto 0)                                 := (others => (others => '0'));
        PCIE_CC_MFB_EOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*max(1, log2(PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE)) -1 downto 0)          := (others => (others => '0'));
        PCIE_CC_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0)                                                                                                    := (others => '0');
        PCIE_CC_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =============================================================================================
        -- MI control interface
        -- =============================================================================================
        MI_ADDR : in  slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_DWR  : in  slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_BE   : in  slv_array_t(DMA_STREAMS -1 downto 0)(32/8 -1 downto 0);
        MI_RD   : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_WR   : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_DRD  : out slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_ARDY : out std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_DRDY : out std_logic_vector(DMA_STREAMS -1 downto 0)
    );
end entity;

architecture CALYPTE of DMA_WRAPPER is

    -- =============================================================================================
    -- Setup constants
    -- =============================================================================================
    constant OUT_PIPE_EN : boolean := TRUE;

    constant MFB_LOOPBACK_EN    : boolean := TRUE;
    constant LATENCY_METER_EN   : boolean := DMA_DEBUG_ENABLE;
    constant TX_DMA_DBG_CORE_EN : boolean := DMA_DEBUG_ENABLE;

    constant ST_SP_DBG_META_WIDTH : natural := 4;

    --==============================================================================================
    --  MI Async and Splitting
    --==============================================================================================
    constant MI_SPLIT_PORTS : natural := 2;
    constant MI_SPLIT_BASES : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH-1 downto 0) := (
        0 => X"00000000",               -- DMA Controller
        1 => X"00300000");              -- DMA Test Core
    constant MI_SPLIT_ADDR_MASK : std_logic_vector(MI_WIDTH -1 downto 0) := X"00300000";

    -- MI split for DMA 0 and TSU
    signal mi_dmagen_dwr  : slv_array_2d_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0)(32-1 downto 0);
    signal mi_dmagen_addr : slv_array_2d_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0)(32-1 downto 0);
    signal mi_dmagen_be   : slv_array_2d_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0)(4-1 downto 0);
    signal mi_dmagen_rd   : slv_array_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0);
    signal mi_dmagen_wr   : slv_array_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0);
    signal mi_dmagen_drd  : slv_array_2d_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0)(32-1 downto 0);
    signal mi_dmagen_ardy : slv_array_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0);
    signal mi_dmagen_drdy : slv_array_t(DMA_STREAMS -1 downto 0)(MI_SPLIT_PORTS -1 downto 0);

    -- MI clocked on PCIE_CLOCK
    signal mi_sync_dwr  : slv_array_t(DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal mi_sync_addr : slv_array_t(DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal mi_sync_be   : slv_array_t(DMA_STREAMS-1 downto 0)(4-1 downto 0);
    signal mi_sync_rd   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal mi_sync_wr   : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal mi_sync_drd  : slv_array_t(DMA_STREAMS-1 downto 0)(32-1 downto 0);
    signal mi_sync_ardy : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal mi_sync_drdy : std_logic_vector(DMA_STREAMS-1 downto 0);

    --==============================================================================================
    --  Testing Module ---> DMA Module interface
    --==============================================================================================
    signal c2h_dma_mfb_meta_hdr_meta_tst : slv_array_t(DMA_STREAMS-1 downto 0)(HDR_META_WIDTH -1 downto 0);
    signal c2h_dma_mfb_meta_channel_tst  : slv_array_t(DMA_STREAMS-1 downto 0)(log2(C2H_CHANNELS) -1 downto 0);

    signal c2h_dma_mfb_data_tst    : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal c2h_dma_mfb_sof_tst     : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_eof_tst     : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal c2h_dma_mfb_sof_pos_tst : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_eof_pos_tst : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal c2h_dma_mfb_src_rdy_tst : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal c2h_dma_mfb_dst_rdy_tst : std_logic_vector(DMA_STREAMS-1 downto 0);

    --==============================================================================================
    --  DMA Module --->  Testing Module interface
    --==============================================================================================
    signal h2c_dma_mfb_meta_size_tst     : slv_array_t(DMA_STREAMS-1 downto 0)(log2(PKT_SIZE_MAX+1)-1 downto 0);
    signal h2c_dma_mfb_meta_hdr_meta_tst : slv_array_t(DMA_STREAMS-1 downto 0)(HDR_META_WIDTH -1 downto 0);
    signal h2c_dma_mfb_meta_channel_tst  : slv_array_t(DMA_STREAMS-1 downto 0)(log2(H2C_CHANNELS) -1 downto 0);

    signal h2c_dma_mfb_data_tst    : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH-1 downto 0);
    signal h2c_dma_mfb_sof_tst     : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_eof_tst     : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
    signal h2c_dma_mfb_sof_pos_tst : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_eof_pos_tst : slv_array_t(DMA_STREAMS-1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
    signal h2c_dma_mfb_src_rdy_tst : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal h2c_dma_mfb_dst_rdy_tst : std_logic_vector(DMA_STREAMS-1 downto 0);

    -- =============================================================================================
    -- Piped PCIE interfaces
    -- =============================================================================================
    signal pcie_rq_mfb_data_piped    : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH -1 downto 0);
    signal pcie_rq_mfb_meta_piped    : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
    signal pcie_rq_mfb_sof_piped     : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0);
    signal pcie_rq_mfb_eof_piped     : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0);
    signal pcie_rq_mfb_sof_pos_piped : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE)) -1 downto 0);
    signal pcie_rq_mfb_eof_pos_piped : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE)) -1 downto 0);
    signal pcie_rq_mfb_src_rdy_piped : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal pcie_rq_mfb_dst_rdy_piped : std_logic_vector(DMA_STREAMS-1 downto 0);

    signal pcie_cq_mfb_data_piped    : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH -1 downto 0);
    signal pcie_cq_mfb_meta_piped    : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
    signal pcie_cq_mfb_sof_piped     : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
    signal pcie_cq_mfb_eof_piped     : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
    signal pcie_cq_mfb_sof_pos_piped : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE)) -1 downto 0);
    signal pcie_cq_mfb_eof_pos_piped : slv_array_t(DMA_STREAMS-1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE)) -1 downto 0);
    signal pcie_cq_mfb_src_rdy_piped : std_logic_vector(DMA_STREAMS-1 downto 0);
    signal pcie_cq_mfb_dst_rdy_piped : std_logic_vector(DMA_STREAMS-1 downto 0);

    --==============================================================================================
    -- Miscelaneous signals
    --==============================================================================================
    signal h2c_dma_mfb_meta_int : slv_array_t(DMA_STREAMS -1 downto 0)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto 0);

    -- =============================================================================================
    -- Debugging signals
    -- =============================================================================================
    signal st_sp_dbg_chan  : slv_array_t(DMA_STREAMS -1 downto 0)(log2(H2C_CHANNELS) -1 downto 0);
    signal st_sp_dbg_meta  : slv_array_t(DMA_STREAMS -1 downto 0)(ST_SP_DBG_META_WIDTH -1 downto 0);
    signal force_reset_dbg : std_logic_vector(DMA_STREAMS-1 downto 0);
begin

    dma_pcie_endp_g : for i in 0 to DMA_STREAMS-1 generate

        --==========================================================================================
        --  MI Splitting and CDC
        --==========================================================================================
        -- splitting the MI bus for the DMA Calypte and TX Testing core.
        -- The Splitter only makes sense when TX direction is enabled, while at that case, both, the
        -- MFB_LOOPBACK and the TX_DEBUG_CORE can be enabled.
        mi_gen_spl_i : entity work.MI_SPLITTER_PLUS_GEN
            generic map(
                ADDR_WIDTH => MI_WIDTH,
                DATA_WIDTH => MI_WIDTH,
                META_WIDTH => 0,
                PORTS      => MI_SPLIT_PORTS,
                PIPE_OUT   => (others => FALSE),

                ADDR_MASK  => MI_SPLIT_ADDR_MASK,
                ADDR_BASES => MI_SPLIT_PORTS,
                ADDR_BASE  => MI_SPLIT_BASES,

                DEVICE => DEVICE
            )
            port map(
                CLK   => MI_CLK,
                RESET => MI_RESET,

                RX_DWR  => MI_DWR(i),
                RX_MWR  => (others => '0'),
                RX_ADDR => MI_ADDR(i),
                RX_BE   => MI_BE(i),
                RX_RD   => MI_RD(i),
                RX_WR   => MI_WR(i),
                RX_ARDY => MI_ARDY(i),
                RX_DRD  => MI_DRD(i),
                RX_DRDY => MI_DRDY(i),

                TX_DWR  => mi_dmagen_dwr(i),
                TX_MWR  => open,
                TX_ADDR => mi_dmagen_addr(i),
                TX_BE   => mi_dmagen_be(i),
                TX_RD   => mi_dmagen_rd(i),
                TX_WR   => mi_dmagen_wr(i),
                TX_ARDY => mi_dmagen_ardy(i),
                TX_DRD  => mi_dmagen_drd(i),
                TX_DRDY => mi_dmagen_drdy(i));

        -- syncing the MI data to the clock which drives the DMA Calypte MI bus
        mi_async_i : entity work.MI_ASYNC
            generic map(
                ADDR_WIDTH => MI_WIDTH,
                DATA_WIDTH => MI_WIDTH,
                DEVICE     => DEVICE
            )
            port map(
                CLK_M     => MI_CLK,
                RESET_M   => MI_RESET,
                MI_M_ADDR => mi_dmagen_addr(i)(0),
                MI_M_DWR  => mi_dmagen_dwr(i)(0),
                MI_M_BE   => mi_dmagen_be(i)(0),
                MI_M_RD   => mi_dmagen_rd(i)(0),
                MI_M_WR   => mi_dmagen_wr(i)(0),
                MI_M_ARDY => mi_dmagen_ardy(i)(0),
                MI_M_DRDY => mi_dmagen_drdy(i)(0),
                MI_M_DRD  => mi_dmagen_drd(i)(0),

                CLK_S     => DMA_CLK(i),
                RESET_S   => DMA_RESET(i),
                MI_S_ADDR => mi_sync_addr(i),
                MI_S_DWR  => mi_sync_dwr(i),
                MI_S_BE   => mi_sync_be(i),
                MI_S_RD   => mi_sync_rd(i),
                MI_S_WR   => mi_sync_wr(i),
                MI_S_ARDY => mi_sync_ardy(i),
                MI_S_DRDY => mi_sync_drdy(i),
                MI_S_DRD  => mi_sync_drd (i)
            );

        -- =========================================================================================
        -- Testing Core
        -- =========================================================================================
        dma_test_core_i : entity work.DMA_TEST_CORE
            generic map (
                DEVICE => DEVICE,

                MFB_REGIONS     => DMA_MFB_REGIONS,
                MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,

                HDR_META_WIDTH => HDR_META_WIDTH,

                RX_CHANNELS => C2H_CHANNELS,
                TX_CHANNELS => H2C_CHANNELS,

                USR_RX_PKT_SIZE_MAX => PKT_SIZE_MAX,
                USR_TX_PKT_SIZE_MAX => PKT_SIZE_MAX,

                MFB_LOOPBACK_EN    => MFB_LOOPBACK_EN,
                LATENCY_METER_EN   => LATENCY_METER_EN,
                TX_DMA_DBG_CORE_EN => TX_DMA_DBG_CORE_EN,

                ST_SP_DBG_SIGNAL_W => ST_SP_DBG_META_WIDTH,
                MI_WIDTH           => MI_WIDTH
            )
            port map (
                CLK   => DMA_CLK(i),
                RESET => DMA_RESET(i),

                ST_SP_DBG_CHAN => st_sp_dbg_chan(i),
                ST_SP_DBG_META => st_sp_dbg_meta(i),
                FORCE_RESET    => force_reset_dbg(i),

                RX_MFB_DATA_IN    => C2H_DMA_MFB_DATA(i),
                RX_MFB_META_IN    => C2H_DMA_MFB_META_PKT_SIZE(i) & C2H_DMA_MFB_META_HDR_META(i) & C2H_DMA_MFB_META_CHAN(i),
                RX_MFB_SOF_IN     => C2H_DMA_MFB_SOF(i),
                RX_MFB_EOF_IN     => C2H_DMA_MFB_EOF(i),
                RX_MFB_SOF_POS_IN => C2H_DMA_MFB_SOF_POS(i),
                RX_MFB_EOF_POS_IN => C2H_DMA_MFB_EOF_POS(i),
                RX_MFB_SRC_RDY_IN => C2H_DMA_MFB_SRC_RDY(i),
                RX_MFB_DST_RDY_IN => C2H_DMA_MFB_DST_RDY(i),

                RX_MFB_META_PKT_SIZE_OUT => open,
                RX_MFB_META_HDR_META_OUT => c2h_dma_mfb_meta_hdr_meta_tst(i),
                RX_MFB_META_CHAN_OUT     => c2h_dma_mfb_meta_channel_tst(i),

                RX_MFB_DATA_OUT    => c2h_dma_mfb_data_tst(i),
                RX_MFB_SOF_OUT     => c2h_dma_mfb_sof_tst(i),
                RX_MFB_EOF_OUT     => c2h_dma_mfb_eof_tst(i),
                RX_MFB_SOF_POS_OUT => c2h_dma_mfb_sof_pos_tst(i),
                RX_MFB_EOF_POS_OUT => c2h_dma_mfb_eof_pos_tst(i),
                RX_MFB_SRC_RDY_OUT => c2h_dma_mfb_src_rdy_tst(i),
                RX_MFB_DST_RDY_OUT => c2h_dma_mfb_dst_rdy_tst(i),

                TX_MFB_DATA_OUT    => H2C_DMA_MFB_DATA(i),
                TX_MFB_META_OUT    => h2c_dma_mfb_meta_int(i),
                TX_MFB_SOF_OUT     => H2C_DMA_MFB_SOF(i),
                TX_MFB_EOF_OUT     => H2C_DMA_MFB_EOF(i),
                TX_MFB_SOF_POS_OUT => H2C_DMA_MFB_SOF_POS(i),
                TX_MFB_EOF_POS_OUT => H2C_DMA_MFB_EOF_POS(i),
                TX_MFB_SRC_RDY_OUT => H2C_DMA_MFB_SRC_RDY(i),
                TX_MFB_DST_RDY_OUT => H2C_DMA_MFB_DST_RDY(i),

                TX_MFB_META_PKT_SIZE_IN => h2c_dma_mfb_meta_size_tst(i),
                TX_MFB_META_HDR_META_IN => h2c_dma_mfb_meta_hdr_meta_tst(i),
                TX_MFB_META_CHAN_IN     => h2c_dma_mfb_meta_channel_tst(i),

                TX_MFB_DATA_IN    => h2c_dma_mfb_data_tst(i),
                TX_MFB_SOF_IN     => h2c_dma_mfb_sof_tst(i),
                TX_MFB_EOF_IN     => h2c_dma_mfb_eof_tst(i),
                TX_MFB_SOF_POS_IN => h2c_dma_mfb_sof_pos_tst(i),
                TX_MFB_EOF_POS_IN => h2c_dma_mfb_eof_pos_tst(i),
                TX_MFB_SRC_RDY_IN => h2c_dma_mfb_src_rdy_tst(i),
                TX_MFB_DST_RDY_IN => h2c_dma_mfb_dst_rdy_tst(i),

                MI_CLK   => MI_CLK,
                MI_RESET => MI_RESET,

                MI_ADDR => mi_dmagen_addr(i)(1),
                MI_DWR  => mi_dmagen_dwr(i)(1),
                MI_BE   => mi_dmagen_be(i)(1),
                MI_RD   => mi_dmagen_rd(i)(1),
                MI_WR   => mi_dmagen_wr(i)(1),
                MI_ARDY => mi_dmagen_ardy(i)(1),
                MI_DRD  => mi_dmagen_drd(i)(1),
                MI_DRDY => mi_dmagen_drdy(i)(1)
            );

        H2C_DMA_MFB_META_PKT_SIZE(i) <= h2c_dma_mfb_meta_int(i)(log2(PKT_SIZE_MAX+1) + HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto HDR_META_WIDTH + log2(H2C_CHANNELS));
        H2C_DMA_MFB_META_HDR_META(i) <= h2c_dma_mfb_meta_int(i)(HDR_META_WIDTH + log2(H2C_CHANNELS) -1 downto log2(H2C_CHANNELS));
        H2C_DMA_MFB_META_CHAN(i)     <= h2c_dma_mfb_meta_int(i)(log2(H2C_CHANNELS) -1 downto 0);

        --==============================================================================================
        --  DMA Calypte Module
        --==============================================================================================
        dma_calypte_i : entity work.DMA_CALYPTE
            generic map(
                DEVICE => DEVICE,

                USR_MFB_REGIONS     => DMA_MFB_REGIONS,
                USR_MFB_REGION_SIZE => DMA_MFB_REGION_SIZE,
                USR_MFB_BLOCK_SIZE  => DMA_MFB_BLOCK_SIZE,
                USR_MFB_ITEM_WIDTH  => DMA_MFB_ITEM_WIDTH,

                PCIE_RQ_MFB_REGIONS     => PCIE_RQ_MFB_REGIONS,
                PCIE_RQ_MFB_REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
                PCIE_RQ_MFB_BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
                PCIE_RQ_MFB_ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

                PCIE_CQ_MFB_REGIONS     => PCIE_CQ_MFB_REGIONS,
                PCIE_CQ_MFB_REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
                PCIE_CQ_MFB_BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
                PCIE_CQ_MFB_ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

                HDR_META_WIDTH => HDR_META_WIDTH,

                RX_CHANNELS         => C2H_CHANNELS,
                RX_PTR_WIDTH        => C2H_PTR_WIDTH,
                USR_RX_PKT_SIZE_MAX => PKT_SIZE_MAX,
                TRBUF_REG_EN        => TRUE,
                PERF_CNTR_EN        => DMA_DEBUG_ENABLE,

                TX_CHANNELS         => H2C_CHANNELS,
                TX_PTR_WIDTH        => H2C_PTR_WIDTH,
                USR_TX_PKT_SIZE_MAX => PKT_SIZE_MAX,

                DSP_CNT_WIDTH => DSP_CNT_WIDTH,

                RX_GEN_EN => C2H_GEN_EN,
                TX_GEN_EN => H2C_GEN_EN,

                ST_SP_DBG_SIGNAL_W => ST_SP_DBG_META_WIDTH,
                MI_WIDTH           => MI_WIDTH
            )
            port map(
                CLK   => DMA_CLK(i),
                RESET => DMA_RESET(i) or force_reset_dbg(i),

                USR_RX_MFB_META_HDR_META => c2h_dma_mfb_meta_hdr_meta_tst(i),
                USR_RX_MFB_META_CHAN     => c2h_dma_mfb_meta_channel_tst(i),

                USR_RX_MFB_DATA    => c2h_dma_mfb_data_tst(i),
                USR_RX_MFB_SOF     => c2h_dma_mfb_sof_tst(i),
                USR_RX_MFB_EOF     => c2h_dma_mfb_eof_tst(i),
                USR_RX_MFB_SOF_POS => c2h_dma_mfb_sof_pos_tst(i),
                USR_RX_MFB_EOF_POS => c2h_dma_mfb_eof_pos_tst(i),
                USR_RX_MFB_SRC_RDY => c2h_dma_mfb_src_rdy_tst(i),
                USR_RX_MFB_DST_RDY => c2h_dma_mfb_dst_rdy_tst(i),

                USR_TX_MFB_META_PKT_SIZE => h2c_dma_mfb_meta_size_tst(i),
                USR_TX_MFB_META_HDR_META => h2c_dma_mfb_meta_hdr_meta_tst(i),
                USR_TX_MFB_META_CHAN     => h2c_dma_mfb_meta_channel_tst(i),

                USR_TX_MFB_DATA    => h2c_dma_mfb_data_tst(i),
                USR_TX_MFB_SOF     => h2c_dma_mfb_sof_tst(i),
                USR_TX_MFB_EOF     => h2c_dma_mfb_eof_tst(i),
                USR_TX_MFB_SOF_POS => h2c_dma_mfb_sof_pos_tst(i),
                USR_TX_MFB_EOF_POS => h2c_dma_mfb_eof_pos_tst(i),
                USR_TX_MFB_SRC_RDY => h2c_dma_mfb_src_rdy_tst(i),
                USR_TX_MFB_DST_RDY => h2c_dma_mfb_dst_rdy_tst(i),

                ST_SP_DBG_CHAN => st_sp_dbg_chan(i),
                ST_SP_DBG_META => st_sp_dbg_meta(i),

                PCIE_RQ_MFB_DATA    => pcie_rq_mfb_data_piped(i),
                PCIE_RQ_MFB_META    => pcie_rq_mfb_meta_piped(i),
                PCIE_RQ_MFB_SOF     => pcie_rq_mfb_sof_piped(i),
                PCIE_RQ_MFB_EOF     => pcie_rq_mfb_eof_piped(i),
                PCIE_RQ_MFB_SOF_POS => pcie_rq_mfb_sof_pos_piped(i),
                PCIE_RQ_MFB_EOF_POS => pcie_rq_mfb_eof_pos_piped(i),
                PCIE_RQ_MFB_SRC_RDY => pcie_rq_mfb_src_rdy_piped(i),
                PCIE_RQ_MFB_DST_RDY => pcie_rq_mfb_dst_rdy_piped(i),

                PCIE_CQ_MFB_DATA    => pcie_cq_mfb_data_piped(i),
                PCIE_CQ_MFB_META    => pcie_cq_mfb_meta_piped(i),
                PCIE_CQ_MFB_SOF     => pcie_cq_mfb_sof_piped(i),
                PCIE_CQ_MFB_EOF     => pcie_cq_mfb_eof_piped(i),
                PCIE_CQ_MFB_SOF_POS => pcie_cq_mfb_sof_pos_piped(i),
                PCIE_CQ_MFB_EOF_POS => pcie_cq_mfb_eof_pos_piped(i),
                PCIE_CQ_MFB_SRC_RDY => pcie_cq_mfb_src_rdy_piped(i),
                PCIE_CQ_MFB_DST_RDY => pcie_cq_mfb_dst_rdy_piped(i),

                MI_ADDR => mi_sync_addr(i),
                MI_DWR  => mi_sync_dwr(i),
                MI_BE   => mi_sync_be(i),
                MI_RD   => mi_sync_rd(i),
                MI_WR   => mi_sync_wr(i),
                MI_DRD  => mi_sync_drd(i),
                MI_ARDY => mi_sync_ardy(i),
                MI_DRDY => mi_sync_drdy(i));

        pcie_rq_mfb_pipe_i : entity work.MFB_PIPE
            generic map (
                REGIONS     => PCIE_RQ_MFB_REGIONS,
                REGION_SIZE => PCIE_RQ_MFB_REGION_SIZE,
                BLOCK_SIZE  => PCIE_RQ_MFB_BLOCK_SIZE,
                ITEM_WIDTH  => PCIE_RQ_MFB_ITEM_WIDTH,

                META_WIDTH  => PCIE_RQ_META_WIDTH,
                FAKE_PIPE   => (not OUT_PIPE_EN) or (not C2H_GEN_EN),
                USE_DST_RDY => TRUE,
                PIPE_TYPE   => "REG",
                DEVICE      => DEVICE)
            port map (
                CLK   => DMA_CLK(i),
                RESET => DMA_RESET(i),

                RX_DATA    => pcie_rq_mfb_data_piped(i),
                RX_META    => pcie_rq_mfb_meta_piped(i),
                RX_SOF_POS => pcie_rq_mfb_sof_pos_piped(i),
                RX_EOF_POS => pcie_rq_mfb_eof_pos_piped(i),
                RX_SOF     => pcie_rq_mfb_sof_piped(i),
                RX_EOF     => pcie_rq_mfb_eof_piped(i),
                RX_SRC_RDY => pcie_rq_mfb_src_rdy_piped(i),
                RX_DST_RDY => pcie_rq_mfb_dst_rdy_piped(i),

                TX_DATA    => PCIE_RQ_MFB_DATA(i),
                TX_META    => PCIE_RQ_MFB_META(i),
                TX_SOF_POS => PCIE_RQ_MFB_SOF_POS(i),
                TX_EOF_POS => PCIE_RQ_MFB_EOF_POS(i),
                TX_SOF     => PCIE_RQ_MFB_SOF(i),
                TX_EOF     => PCIE_RQ_MFB_EOF(i),
                TX_SRC_RDY => PCIE_RQ_MFB_SRC_RDY(i),
                TX_DST_RDY => PCIE_RQ_MFB_DST_RDY(i));

        pcie_cq_mfb_pipe_i : entity work.MFB_PIPE
            generic map (
                REGIONS     => PCIE_CQ_MFB_REGIONS,
                REGION_SIZE => PCIE_CQ_MFB_REGION_SIZE,
                BLOCK_SIZE  => PCIE_CQ_MFB_BLOCK_SIZE,
                ITEM_WIDTH  => PCIE_CQ_MFB_ITEM_WIDTH,

                META_WIDTH  => PCIE_CQ_META_WIDTH,
                FAKE_PIPE   => (not OUT_PIPE_EN) or (not H2C_GEN_EN),
                USE_DST_RDY => TRUE,
                PIPE_TYPE   => "REG",
                DEVICE      => DEVICE)
            port map (
                CLK   => DMA_CLK(i),
                RESET => DMA_RESET(i),

                RX_DATA    => PCIE_CQ_MFB_DATA(i),
                RX_META    => PCIE_CQ_MFB_META(i),
                RX_SOF_POS => PCIE_CQ_MFB_SOF_POS(i),
                RX_EOF_POS => PCIE_CQ_MFB_EOF_POS(i),
                RX_SOF     => PCIE_CQ_MFB_SOF(i),
                RX_EOF     => PCIE_CQ_MFB_EOF(i),
                RX_SRC_RDY => PCIE_CQ_MFB_SRC_RDY(i),
                RX_DST_RDY => PCIE_CQ_MFB_DST_RDY(i),

                TX_DATA    => pcie_cq_mfb_data_piped(i),
                TX_META    => pcie_cq_mfb_meta_piped(i),
                TX_SOF_POS => pcie_cq_mfb_sof_pos_piped(i),
                TX_EOF_POS => pcie_cq_mfb_eof_pos_piped(i),
                TX_SOF     => pcie_cq_mfb_sof_piped(i),
                TX_EOF     => pcie_cq_mfb_eof_piped(i),
                TX_SRC_RDY => pcie_cq_mfb_src_rdy_piped(i),
                TX_DST_RDY => pcie_cq_mfb_dst_rdy_piped(i));
    end generate;
end architecture;
