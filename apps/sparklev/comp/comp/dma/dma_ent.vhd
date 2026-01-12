-- dma_ent.vhd: DMA Module Entity
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause OR CERN-OHL-P-2.0

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

-- =========================================================================
--                                 Description
-- =========================================================================
-- Top level of the DMA Module, containing also Generator/Loopback Switch
entity DMA is
    generic(
        -- =====================================================================
        --  DMA Module generics
        -- =====================================================================
        -- For description see entity of the used DMA Module
        DEVICE : string := "ULTRASCALE";

        -- Number of independent DMA streams
        DMA_STREAMS : natural := 1;

        DMA_MFB_REGIONS     : natural := 1;
        DMA_MFB_REGION_SIZE : natural := 4;
        DMA_MFB_BLOCK_SIZE  : natural := 8;
        DMA_MFB_ITEM_WIDTH  : natural := 8;

        PCIE_RQ_MFB_REGIONS     : natural := 1;
        PCIE_RQ_MFB_REGION_SIZE : natural := 1;
        PCIE_RQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RQ_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_RC_MFB_REGIONS     : natural := 1;
        PCIE_RC_MFB_REGION_SIZE : natural := 1;
        PCIE_RC_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_RC_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_CQ_MFB_REGIONS     : natural := 1;
        PCIE_CQ_MFB_REGION_SIZE : natural := 1;
        PCIE_CQ_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CQ_MFB_ITEM_WIDTH  : natural := 32;

        PCIE_CC_MFB_REGIONS     : natural := 1;
        PCIE_CC_MFB_REGION_SIZE : natural := 1;
        PCIE_CC_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_CC_MFB_ITEM_WIDTH  : natural := 32;

        HDR_META_WIDTH : natural := 24;
        PKT_SIZE_MAX   : natural := 2**12;

        C2H_CHANNELS  : natural := 8;
        C2H_PTR_WIDTH : natural := 16;

        H2C_CHANNELS  : natural := 8;
        H2C_PTR_WIDTH : natural := 13;

        C2H_GEN_EN : boolean := TRUE;
        H2C_GEN_EN : boolean := TRUE;

        -- =====================================================================
        --  Others
        -- =====================================================================
        -- Enabled debug components for DMA
        DMA_DEBUG_ENABLE : boolean := FALSE;
        -- Enable presence of Generator/Loopback Switch
        GEN_LOOP_EN      : boolean := TRUE
    -- =====================================================================
    );
    port(
        -- =====================================================================
        --  Clock and Reset
        -- =====================================================================
        -- Clock for MI interface
        MI_CLK    : in std_logic;
        MI_RESET  : in std_logic;
        -- Clock for the User-side interface
        DMA_CLK   : in std_logic_vector(DMA_STREAMS -1 downto 0);
        DMA_RESET : in std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =====================================================================
        --  Card-to-Host DMA 
        -- =====================================================================
        C2H_DMA_MFB_META_HDR_META : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
        C2H_DMA_MFB_META_CHAN     : in slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(C2H_CHANNELS) -1 downto 0);

        C2H_DMA_MFB_DATA    : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto 0);
        C2H_DMA_MFB_SOF     : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        C2H_DMA_MFB_EOF     : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        C2H_DMA_MFB_SOF_POS : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
        C2H_DMA_MFB_EOF_POS : in  slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
        C2H_DMA_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        C2H_DMA_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =====================================================================
        --  Host-to-Card DMA
        -- =====================================================================
        H2C_DMA_MFB_META_PKT_SIZE : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(PKT_SIZE_MAX+1) -1 downto 0);
        H2C_DMA_MFB_META_HDR_META : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*HDR_META_WIDTH -1 downto 0);
        H2C_DMA_MFB_META_CHAN     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*log2(H2C_CHANNELS) -1 downto 0);

        H2C_DMA_MFB_DATA    : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE*DMA_MFB_ITEM_WIDTH -1 downto 0);
        H2C_DMA_MFB_SOF     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        H2C_DMA_MFB_EOF     : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS -1 downto 0);
        H2C_DMA_MFB_SOF_POS : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE)) -1 downto 0);
        H2C_DMA_MFB_EOF_POS : out slv_array_t(DMA_STREAMS -1 downto 0)(DMA_MFB_REGIONS*max(1, log2(DMA_MFB_REGION_SIZE*DMA_MFB_BLOCK_SIZE)) -1 downto 0);
        H2C_DMA_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);
        H2C_DMA_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =====================================================================
        --  PCIe-side interfaces
        -- =====================================================================
        -- Upstream MFB interface (for sending data to PCIe Endpoints)
        PCIE_RQ_MFB_DATA    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE*PCIE_RQ_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_RQ_MFB_META    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH -1 downto 0);
        PCIE_RQ_MFB_SOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_EOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS -1 downto 0);
        PCIE_RQ_MFB_SOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_EOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RQ_MFB_REGIONS*max(1, log2(PCIE_RQ_MFB_REGION_SIZE*PCIE_RQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RQ_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_RQ_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- Downstream MFB interface (for sending data from PCIe Endpoints)
        PCIE_RC_MFB_DATA    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE*PCIE_RC_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_RC_MFB_SOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS -1 downto 0);
        PCIE_RC_MFB_EOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS -1 downto 0);
        PCIE_RC_MFB_SOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*max(1, log2(PCIE_RC_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_RC_MFB_EOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_RC_MFB_REGIONS*max(1, log2(PCIE_RC_MFB_REGION_SIZE*PCIE_RC_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_RC_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_RC_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);

        -- CQ MFB interface (receiving data from PCIe endpoint, DMA Calypte only)
        PCIE_CQ_MFB_DATA    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE*PCIE_CQ_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_CQ_MFB_META    : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH -1 downto 0);
        PCIE_CQ_MFB_SOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_EOF     : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS -1 downto 0);
        PCIE_CQ_MFB_SOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_EOF_POS : in  slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CQ_MFB_REGIONS*max(1, log2(PCIE_CQ_MFB_REGION_SIZE*PCIE_CQ_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_CQ_MFB_SRC_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_CQ_MFB_DST_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);

        -- CC MFB interface (seinding data to PCIe endpoint, DMA Calypte only)
        PCIE_CC_MFB_DATA    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE*PCIE_CC_MFB_ITEM_WIDTH -1 downto 0);
        PCIE_CC_MFB_META    : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*PCIE_CC_META_WIDTH -1 downto 0);
        PCIE_CC_MFB_SOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS -1 downto 0);
        PCIE_CC_MFB_EOF     : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS -1 downto 0);
        PCIE_CC_MFB_SOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*max(1, log2(PCIE_CC_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_CC_MFB_EOF_POS : out slv_array_t (DMA_STREAMS -1 downto 0)(PCIE_CC_MFB_REGIONS*max(1, log2(PCIE_CC_MFB_REGION_SIZE*PCIE_CC_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_CC_MFB_SRC_RDY : out std_logic_vector(DMA_STREAMS -1 downto 0);
        PCIE_CC_MFB_DST_RDY : in  std_logic_vector(DMA_STREAMS -1 downto 0);

        -- =========================================================================================
        -- MI control interface (for SW access)
        -- =========================================================================================
        -- MI Address Space:
        --     bit 22 -> 0
        --     For register map, see entity of used DMA Module
        MI_ADDR : in  slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_DWR  : in  slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_BE   : in  slv_array_t(DMA_STREAMS -1 downto 0)(32/8 -1 downto 0);
        MI_RD   : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_WR   : in  std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_DRD  : out slv_array_t(DMA_STREAMS -1 downto 0)(32 -1 downto 0);
        MI_ARDY : out std_logic_vector(DMA_STREAMS -1 downto 0);
        MI_DRDY : out std_logic_vector(DMA_STREAMS -1 downto 0);

        -- MI interface for SW access to Generator/Loopback Switch
        -- MI Address Space:
        --     bit 22 -> 1
        --     For register map, see entity of used Generator/Loopback Switch (GLS) module
        --     TODO: This ports should also be dependant on the amount of DMA streams
        GEN_LOOP_MI_ADDR : in  std_logic_vector(32 -1 downto 0);
        GEN_LOOP_MI_DWR  : in  std_logic_vector(32 -1 downto 0);
        GEN_LOOP_MI_BE   : in  std_logic_vector(32/8-1 downto 0);
        GEN_LOOP_MI_RD   : in  std_logic;
        GEN_LOOP_MI_WR   : in  std_logic;
        GEN_LOOP_MI_DRD  : out std_logic_vector(32 -1 downto 0);
        GEN_LOOP_MI_ARDY : out std_logic;
        GEN_LOOP_MI_DRDY : out std_logic
    );
end entity;
