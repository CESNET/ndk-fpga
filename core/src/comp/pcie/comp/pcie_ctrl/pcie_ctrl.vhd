-- pcie_ctrl.vhd: PCIe module controllers
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;
use work.pcie_meta_pack.all;

entity PCIE_CTRL is
    generic(
        -- =====================================================================
        -- BAR base address configuration
        -- =====================================================================
        BAR0_BASE_ADDR      : std_logic_vector(31 downto 0) := X"01000000";
        BAR1_BASE_ADDR      : std_logic_vector(31 downto 0) := X"02000000";
        BAR2_BASE_ADDR      : std_logic_vector(31 downto 0) := X"03000000";
        BAR3_BASE_ADDR      : std_logic_vector(31 downto 0) := X"04000000";
        BAR4_BASE_ADDR      : std_logic_vector(31 downto 0) := X"05000000";
        BAR5_BASE_ADDR      : std_logic_vector(31 downto 0) := X"06000000";
        EXP_ROM_BASE_ADDR   : std_logic_vector(31 downto 0) := X"0A000000";

        -- =====================================================================
        -- MFB configuration
        -- =====================================================================
        CQ_MFB_REGIONS      : natural := 2;
        CQ_MFB_REGION_SIZE  : natural := 1;
        CQ_MFB_BLOCK_SIZE   : natural := 8;
        CQ_MFB_ITEM_WIDTH   : natural := 32;
        RC_MFB_REGIONS      : natural := 2;
        RC_MFB_REGION_SIZE  : natural := 1;
        RC_MFB_BLOCK_SIZE   : natural := 8;
        RC_MFB_ITEM_WIDTH   : natural := 32;
        RC_MFB_REGIONS_DMA  : natural := RC_MFB_REGIONS;
        CC_MFB_REGIONS      : natural := 2;
        CC_MFB_REGION_SIZE  : natural := 1;
        CC_MFB_BLOCK_SIZE   : natural := 8;
        CC_MFB_ITEM_WIDTH   : natural := 32;
        RQ_MFB_REGIONS      : natural := 2;
        RQ_MFB_REGION_SIZE  : natural := 1;
        RQ_MFB_BLOCK_SIZE   : natural := 8;
        RQ_MFB_ITEM_WIDTH   : natural := 32;
        RQ_MFB_REGIONS_DMA  : natural := RQ_MFB_REGIONS;

        -- =====================================================================
        -- Others configuration
        -- =====================================================================
        -- Number of DMA ports per one PCIe EP (allowed values: 1, 2)
        DMA_PORTS           : natural := 1;
        -- Disable PTC module and allows direct connection of the DMA module to
        -- the PCIe IP RQ and RC interfaces.
        PTC_DISABLE         : boolean := false;
        -- Enable CQ/CC interface for DMA-BAR, DMA_PORTS must be 1
        DMA_BAR_ENABLE      : boolean := false;
        -- Connected PCIe endpoint type
        ENDPOINT_TYPE       : string  := "P_TILE";
        -- FPGA device
        DEVICE              : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        --  CLOCK AND RESETS
        -- =====================================================================
        PCIE_CLK            : in  std_logic;
        PCIE_RESET          : in  std_logic_vector(5-1 downto 0);
        DMA_CLK             : in  std_logic;
        DMA_RESET           : in  std_logic;
        MI_CLK              : in  std_logic;
        MI_RESET            : in  std_logic;

        -- =====================================================================
        --  CONFIGURATION STATUS INTERFACE
        -- =====================================================================
        CTL_MAX_PAYLOAD     : in  std_logic_vector(2 downto 0);
        CTL_BAR_APERTURE    : in  std_logic_vector(5 downto 0);
        CTL_RCB_SIZE        : in  std_logic;

        -- =====================================================================
        -- PCIE RQ MFB interface (PCIE_CLK)
        --
        -- MFB bus for transferring RC PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        PCIE_RQ_MFB_DATA    : out std_logic_vector(RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_RQ_MFB_META    : out std_logic_vector(RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
        PCIE_RQ_MFB_SOF     : out std_logic_vector(RQ_MFB_REGIONS-1 downto 0);
        PCIE_RQ_MFB_EOF     : out std_logic_vector(RQ_MFB_REGIONS-1 downto 0);
        PCIE_RQ_MFB_SOF_POS : out std_logic_vector(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        PCIE_RQ_MFB_EOF_POS : out std_logic_vector(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_RQ_MFB_SRC_RDY : out std_logic;
        PCIE_RQ_MFB_DST_RDY : in  std_logic;

        -- =====================================================================
        -- DMA RQ MFB+MVB interface (PCIE_CLK or DMA_CLK)
        --
        -- PTC ENABLE: MFB+MVB bus for transferring RQ PTC-DMA transactions.
        -- MFB+MVB bus is clocked at DMA_CLK.
        -- PTC DISABLE: MFB bus only for transferring RQ PCIe transactions 
        -- (format according to the PCIe IP used). Compared to the standard MFB
        -- specification, it does not allow gaps (SRC_RDY=0) inside transactions
        -- and requires that the first transaction in a word starts at byte 0.
        -- MFB bus is clocked at PCIE_CLK.
        -- =====================================================================
        DMA_RQ_MFB_DATA     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        DMA_RQ_MFB_META     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA*PCIE_RQ_META_WIDTH-1 downto 0);
        DMA_RQ_MFB_SOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA-1 downto 0);
        DMA_RQ_MFB_EOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA-1 downto 0);
        DMA_RQ_MFB_SOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        DMA_RQ_MFB_EOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_RQ_MFB_SRC_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RQ_MFB_DST_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);

        DMA_RQ_MVB_DATA     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA*DMA_UPHDR_WIDTH-1 downto 0);
        DMA_RQ_MVB_VLD      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS_DMA-1 downto 0);
        DMA_RQ_MVB_SRC_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RQ_MVB_DST_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);

        -- =====================================================================
        -- PCIE RC MFB interface (PCIE_CLK)
        --
        -- MFB bus for transferring RC PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        PCIE_RC_MFB_DATA    : in  std_logic_vector(RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_RC_MFB_META    : in  std_logic_vector(RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
        PCIE_RC_MFB_SOF     : in  std_logic_vector(RC_MFB_REGIONS-1 downto 0);
        PCIE_RC_MFB_EOF     : in  std_logic_vector(RC_MFB_REGIONS-1 downto 0);
        PCIE_RC_MFB_SOF_POS : in  std_logic_vector(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        PCIE_RC_MFB_EOF_POS : in  std_logic_vector(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_RC_MFB_SRC_RDY : in  std_logic;
        PCIE_RC_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- DMA RC MFB+MVB interface (PCIE_CLK or DMA_CLK)
        --
        -- PTC ENABLE: MFB+MVB bus for transferring RC PTC-DMA transactions.
        -- MFB+MVB bus is clocked at DMA_CLK.
        -- PTC DISABLE: MFB bus only for transferring RC PCIe transactions 
        -- (format according to the PCIe IP used). Compared to the standard MFB
        -- specification, it does not allow gaps (SRC_RDY=0) inside transactions
        -- and requires that the first transaction in a word starts at byte 0.
        -- MFB bus is clocked at PCIE_CLK.
        -- =====================================================================
        DMA_RC_MFB_DATA     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        DMA_RC_MFB_META     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA*PCIE_RC_META_WIDTH-1 downto 0);
        DMA_RC_MFB_SOF      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA-1 downto 0);
        DMA_RC_MFB_EOF      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA-1 downto 0);
        DMA_RC_MFB_SOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        DMA_RC_MFB_EOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_RC_MFB_SRC_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RC_MFB_DST_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);

        DMA_RC_MVB_DATA     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA*DMA_DOWNHDR_WIDTH-1 downto 0);
        DMA_RC_MVB_VLD      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS_DMA-1 downto 0);
        DMA_RC_MVB_SRC_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RC_MVB_DST_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);

        -- =====================================================================
        -- PCIE CQ MFB interface (PCIE_CLK)
        --
        -- MFB bus for transferring CQ PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        PCIE_CQ_MFB_DATA    : in  std_logic_vector(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_CQ_MFB_META    : in  std_logic_vector(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        PCIE_CQ_MFB_SOF     : in  std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
        PCIE_CQ_MFB_EOF     : in  std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
        PCIE_CQ_MFB_SOF_POS : in  std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
        PCIE_CQ_MFB_EOF_POS : in  std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_CQ_MFB_SRC_RDY : in  std_logic;
        PCIE_CQ_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- DMA CQ MFB interface - DMA-BAR (PCIE_CLK)
        --
        -- MFB bus for transferring CQ DMA-BAR PCIe transactions (format
        -- according to the PCIe IP used). Compared to the standard MFB
        -- specification, it does not allow gaps (SRC_RDY=0) inside transactions
        -- and requires that the first transaction in a word starts at byte 0.
        -- =====================================================================
        DMA_CQ_MFB_DATA     : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
        DMA_CQ_MFB_META     : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        DMA_CQ_MFB_SOF      : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        DMA_CQ_MFB_EOF      : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        DMA_CQ_MFB_SOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
        DMA_CQ_MFB_EOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_CQ_MFB_SRC_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_CQ_MFB_DST_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);

        -- =====================================================================
        -- PCIE CC MFB interface (PCIE_CLK)
        --
        -- MFB bus for transferring CC PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        PCIE_CC_MFB_DATA    : out std_logic_vector(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_CC_MFB_META    : out std_logic_vector(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        PCIE_CC_MFB_SOF     : out std_logic_vector(CC_MFB_REGIONS-1 downto 0);
        PCIE_CC_MFB_EOF     : out std_logic_vector(CC_MFB_REGIONS-1 downto 0);
        PCIE_CC_MFB_SOF_POS : out std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
        PCIE_CC_MFB_EOF_POS : out std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
        PCIE_CC_MFB_SRC_RDY : out std_logic;
        PCIE_CC_MFB_DST_RDY : in  std_logic;

        -- =====================================================================
        -- DMA CC MFB interface - DMA-BAR (PCIE_CLK)
        --
        -- MFB bus for transferring CC DMA-BAR PCIe transactions (format
        -- according to the PCIe IP used). Compared to the standard MFB
        -- specification, it does not allow gaps (SRC_RDY=0) inside transactions
        -- and requires that the first transaction in a word starts at byte 0.
        -- =====================================================================
        DMA_CC_MFB_DATA     : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
        DMA_CC_MFB_META     : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        DMA_CC_MFB_SOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        DMA_CC_MFB_EOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        DMA_CC_MFB_SOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
        DMA_CC_MFB_EOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_CC_MFB_SRC_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_CC_MFB_DST_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);

        -- =====================================================================
        --  PCIe tags interface - Xilinx FPGA Only (PCIE_CLK)
        -- =====================================================================
        -- PCIe tag assigned to send transaction
        RQ_TAG_ASSIGN       : in  std_logic_vector(RQ_MFB_REGIONS*8-1 downto 0);
        -- Valid bit for assigned tags
        RQ_TAG_ASSIGN_VLD   : in  std_logic_vector(RQ_MFB_REGIONS-1 downto 0);

        -- =====================================================================
        -- MI32 interface (MI_CLK)
        --
        -- Root of the MI32 bus tree.
        -- =====================================================================
        MI_DWR              : out std_logic_vector(31 downto 0);
        MI_ADDR             : out std_logic_vector(31 downto 0);
        MI_BE               : out std_logic_vector(3 downto 0);
        MI_RD               : out std_logic;
        MI_WR               : out std_logic;
        MI_DRD              : in  std_logic_vector(31 downto 0);
        MI_ARDY             : in  std_logic;
        MI_DRDY             : in  std_logic;

        -- MI debug interface
        MI_DBG_DWR          : in  std_logic_vector(31 downto 0);
        MI_DBG_ADDR         : in  std_logic_vector(31 downto 0);
        MI_DBG_BE           : in  std_logic_vector(3 downto 0);
        MI_DBG_RD           : in  std_logic;
        MI_DBG_WR           : in  std_logic;
        MI_DBG_DRD          : out std_logic_vector(31 downto 0);
        MI_DBG_ARDY         : out std_logic;
        MI_DBG_DRDY         : out std_logic
    );
end entity;

architecture FULL of PCIE_CTRL is

    constant CC_MFB_MERGER_CNT_MAX : natural := 4;

    constant DEBUG_EN              : boolean := PCIE_CTRL_DEBUG_ENABLE;
    -- Number of Streaming Debug Probes for each Master.
    constant DBG_PROBES            : natural := 1;
    -- Address offset for each Streaming Debug Probe.
    constant DBG_PROBE_OFFSET      : natural := 16#40#;
    -- Address offset of all Debug Probes per Endpoint.
    constant DBG_PROBES_OFFSET     : natural := DBG_PROBES*DBG_PROBE_OFFSET;
    -- Name(s) (4-letter IDs) of Streaming Debug Probes.
    -- DRQ0 = DMA RQ 0
    constant DBG_PROBE_STR         : string := "DRQ0";

    function mi_addr_base_f return slv_array_t is
        variable mi_addr_base : slv_array_t(DMA_PORTS-1 downto 0)(31 downto 0);
    begin
        for dp in 0 to DMA_PORTS-1 loop
            mi_addr_base(dp) := std_logic_vector(to_unsigned(dp*DBG_PROBES_OFFSET, 32));
        end loop;
        return mi_addr_base;
    end function;

    signal mtc_cq_mfb_data        : std_logic_vector(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal mtc_cq_mfb_meta        : std_logic_vector(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
    signal mtc_cq_mfb_sof         : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
    signal mtc_cq_mfb_eof         : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
    signal mtc_cq_mfb_sof_pos     : std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
    signal mtc_cq_mfb_eof_pos     : std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal mtc_cq_mfb_src_rdy     : std_logic;
    signal mtc_cq_mfb_dst_rdy     : std_logic;

    signal mtc_fifo_mfb_data        : std_logic_vector(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal mtc_fifo_mfb_meta        : std_logic_vector(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
    signal mtc_fifo_mfb_sof         : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
    signal mtc_fifo_mfb_eof         : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);
    signal mtc_fifo_mfb_sof_pos     : std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
    signal mtc_fifo_mfb_eof_pos     : std_logic_vector(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal mtc_fifo_mfb_src_rdy     : std_logic;
    signal mtc_fifo_mfb_dst_rdy     : std_logic;

    signal mtc_cc_mfb_data        : std_logic_vector(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
    signal mtc_cc_mfb_meta        : std_logic_vector(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
    signal mtc_cc_mfb_sof         : std_logic_vector(CC_MFB_REGIONS-1 downto 0);
    signal mtc_cc_mfb_eof         : std_logic_vector(CC_MFB_REGIONS-1 downto 0);
    signal mtc_cc_mfb_sof_pos     : std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
    signal mtc_cc_mfb_eof_pos     : std_logic_vector(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
    signal mtc_cc_mfb_src_rdy     : std_logic;
    signal mtc_cc_mfb_dst_rdy     : std_logic;

    signal pcie_cq_mfb_meta_arr   : slv_array_t(CQ_MFB_REGIONS-1 downto 0)(PCIE_CQ_META_WIDTH-1 downto 0);
    signal pcie_cq_mfb_data_arr   : slv_array_t(CQ_MFB_REGIONS-1 downto 0)(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal pcie_cq_mfb_bar        : slv_array_t(CQ_MFB_REGIONS-1 downto 0)(PCIE_META_BAR_W-1 downto 0);
    signal pcie_cq_mfb_sel        : std_logic_vector(CQ_MFB_REGIONS-1 downto 0);

    signal pcie_rq_mfb_meta_arr   : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(PCIE_RQ_META_WIDTH-1 downto 0);
    signal pcie_rq_mfb_hdr        : std_logic_vector(RQ_MFB_REGIONS*PCIE_META_REQ_HDR_W-1 downto 0);
    signal pcie_rq_mfb_hdr_arr    : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(PCIE_META_REQ_HDR_W-1 downto 0);
    signal pcie_rq_mfb_prefix     : std_logic_vector(RQ_MFB_REGIONS*PCIE_META_PREFIX_W-1 downto 0);
    signal pcie_rq_mfb_prefix_arr : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(PCIE_META_PREFIX_W-1 downto 0);
    signal pcie_rq_mfb_be         : std_logic_vector(RQ_MFB_REGIONS*8-1 downto 0);
    signal pcie_rq_mfb_be_arr     : slv_array_t(RQ_MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal pcie_rc_mfb_meta_arr   : slv_array_t(RC_MFB_REGIONS-1 downto 0)(PCIE_RC_META_WIDTH-1 downto 0);
    signal pcie_rc_mfb_hdr_arr    : slv_array_t(RC_MFB_REGIONS-1 downto 0)(PCIE_META_CPL_HDR_W-1 downto 0);
    signal pcie_rc_mfb_prefix_arr : slv_array_t(RC_MFB_REGIONS-1 downto 0)(PCIE_META_PREFIX_W-1 downto 0);

    signal ctl_max_payload_reg    : std_logic_vector(3-1 downto 0);

    signal mtc_mi_dwr             : std_logic_vector(31 downto 0);
    signal mtc_mi_addr            : std_logic_vector(31 downto 0);
    signal mtc_mi_be              : std_logic_vector(3 downto 0);
    signal mtc_mi_rd              : std_logic;
    signal mtc_mi_wr              : std_logic;
    signal mtc_mi_drd             : std_logic_vector(31 downto 0);
    signal mtc_mi_ardy            : std_logic;
    signal mtc_mi_drdy            : std_logic;

    signal mi_sync_dwr            : std_logic_vector(31 downto 0);
    signal mi_sync_addr           : std_logic_vector(31 downto 0);
    signal mi_sync_be             : std_logic_vector(3 downto 0);
    signal mi_sync_rd             : std_logic;
    signal mi_sync_wr             : std_logic;
    signal mi_sync_drd            : std_logic_vector(31 downto 0);
    signal mi_sync_ardy           : std_logic;
    signal mi_sync_drdy           : std_logic;

    --==============================================================================================
    -- Debug signals
    --==============================================================================================
    signal mi_split_dbg_dwr       : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_split_dbg_addr      : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_split_dbg_be        : slv_array_t     (DMA_PORTS-1 downto 0)(3 downto 0);
    signal mi_split_dbg_rd        : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_split_dbg_wr        : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_split_dbg_ardy      : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_split_dbg_drd       : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_split_dbg_drdy      : std_logic_vector(DMA_PORTS-1 downto 0);

    signal mi_sync_dbg_dwr        : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_sync_dbg_addr       : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_sync_dbg_be         : slv_array_t     (DMA_PORTS-1 downto 0)(3 downto 0);
    signal mi_sync_dbg_rd         : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_sync_dbg_wr         : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_sync_dbg_ardy       : std_logic_vector(DMA_PORTS-1 downto 0);
    signal mi_sync_dbg_drd        : slv_array_t     (DMA_PORTS-1 downto 0)(31 downto 0);
    signal mi_sync_dbg_drdy       : std_logic_vector(DMA_PORTS-1 downto 0);

    signal dp_out_src_rdy         : slv_array_t(DMA_PORTS-1 downto 0)(DBG_PROBES-1 downto 0);
    signal dp_out_dst_rdy         : slv_array_t(DMA_PORTS-1 downto 0)(DBG_PROBES-1 downto 0);

begin

    -- =========================================================================
    --  PCIE TRANSACTION CTRL (PTC)
    -- =========================================================================

    ptc_g: if (not PTC_DISABLE) generate
        -- DMA_RQ/RC_* clocked at DMA_CLK
        DMA_RC_MFB_META <= (others => (others => '0'));

        pcie_rq_mfb_hdr_arr    <= slv_array_deser(pcie_rq_mfb_hdr,RQ_MFB_REGIONS);
        pcie_rq_mfb_prefix_arr <= slv_array_deser(pcie_rq_mfb_prefix,RQ_MFB_REGIONS);
        pcie_rq_mfb_be_arr     <= slv_array_deser(pcie_rq_mfb_be,RQ_MFB_REGIONS);

        rq_mfb_meta_g: for i in 0 to RQ_MFB_REGIONS-1 generate    
            pcie_rq_mfb_meta_arr(i)(PCIE_RQ_META_HEADER) <= pcie_rq_mfb_hdr_arr(i);
            pcie_rq_mfb_meta_arr(i)(PCIE_RQ_META_PREFIX) <= pcie_rq_mfb_prefix_arr(i);
            pcie_rq_mfb_meta_arr(i)(PCIE_RQ_META_FBE) <= pcie_rq_mfb_be_arr(i)(PCIE_META_FBE_W-1 downto 0);
            pcie_rq_mfb_meta_arr(i)(PCIE_RQ_META_LBE) <= pcie_rq_mfb_be_arr(i)(PCIE_META_LBE_W+PCIE_META_FBE_W-1 downto PCIE_META_FBE_W);
        end generate;

        PCIE_RQ_MFB_META <= slv_array_ser(pcie_rq_mfb_meta_arr);

        pcie_rc_mfb_meta_arr <= slv_array_deser(PCIE_RC_MFB_META,RC_MFB_REGIONS);

        rc_mfb_meta_g: for i in 0 to RC_MFB_REGIONS-1 generate    
            pcie_rc_mfb_hdr_arr(i)    <= pcie_rc_mfb_meta_arr(i)(PCIE_RC_META_HEADER);
            pcie_rc_mfb_prefix_arr(i) <= pcie_rc_mfb_meta_arr(i)(PCIE_RC_META_PREFIX);
        end generate;

        ptc_i : entity work.PCIE_TRANSACTION_CTRL
        generic map(
            DMA_PORTS            => DMA_PORTS,

            MVB_UP_ITEMS         => RQ_MFB_REGIONS,
            DMA_MVB_UP_ITEMS     => RQ_MFB_REGIONS_DMA,
            MFB_UP_REGIONS       => RQ_MFB_REGIONS,
            DMA_MFB_UP_REGIONS   => RQ_MFB_REGIONS_DMA,
            MFB_UP_REG_SIZE      => RQ_MFB_REGION_SIZE,
            MFB_UP_BLOCK_SIZE    => RQ_MFB_BLOCK_SIZE,
            MFB_UP_ITEM_WIDTH    => RQ_MFB_ITEM_WIDTH,

            MVB_DOWN_ITEMS       => RC_MFB_REGIONS,
            DMA_MVB_DOWN_ITEMS   => RC_MFB_REGIONS_DMA,
            MFB_DOWN_REGIONS     => RC_MFB_REGIONS,
            DMA_MFB_DOWN_REGIONS => RC_MFB_REGIONS_DMA,
            MFB_DOWN_REG_SIZE    => RC_MFB_REGION_SIZE,
            MFB_DOWN_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
            MFB_DOWN_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,

            DOWN_FIFO_ITEMS      => 1024,
            AUTO_ASSIGN_TAGS     => true,

            ENDPOINT_TYPE        => ENDPOINT_TYPE,
            DEVICE               => DEVICE
        )
        port map(
            CLK                => PCIE_CLK,
            RESET              => PCIE_RESET(0),

            CLK_DMA            => DMA_CLK,
            RESET_DMA          => DMA_RESET,

            RQ_MVB_HDR_DATA    => pcie_rq_mfb_hdr,
            RQ_MVB_PREFIX_DATA => pcie_rq_mfb_prefix,
            RQ_MVB_VLD         => open,
            RQ_MFB_DATA        => PCIE_RQ_MFB_DATA,
            RQ_MFB_SOF         => PCIE_RQ_MFB_SOF,
            RQ_MFB_EOF         => PCIE_RQ_MFB_EOF,
            RQ_MFB_SOF_POS     => PCIE_RQ_MFB_SOF_POS,
            RQ_MFB_EOF_POS     => PCIE_RQ_MFB_EOF_POS,
            RQ_MFB_SRC_RDY     => PCIE_RQ_MFB_SRC_RDY,
            RQ_MFB_DST_RDY     => PCIE_RQ_MFB_DST_RDY,
            RQ_MFB_BE          => pcie_rq_mfb_be,

            RC_MVB_HDR_DATA    => slv_array_ser(pcie_rc_mfb_hdr_arr),
            RC_MVB_PREFIX_DATA => slv_array_ser(pcie_rc_mfb_prefix_arr),
            RC_MVB_VLD         => PCIE_RC_MFB_SOF,
            RC_MFB_DATA        => PCIE_RC_MFB_DATA,
            RC_MFB_SOF         => PCIE_RC_MFB_SOF,
            RC_MFB_EOF         => PCIE_RC_MFB_EOF,
            RC_MFB_SOF_POS     => PCIE_RC_MFB_SOF_POS,
            RC_MFB_EOF_POS     => PCIE_RC_MFB_EOF_POS,
            RC_MFB_SRC_RDY     => PCIE_RC_MFB_SRC_RDY,
            RC_MFB_DST_RDY     => PCIE_RC_MFB_DST_RDY,

            UP_MVB_DATA        => DMA_RQ_MVB_DATA,
            UP_MVB_VLD         => DMA_RQ_MVB_VLD,
            UP_MVB_SRC_RDY     => DMA_RQ_MVB_SRC_RDY,
            UP_MVB_DST_RDY     => DMA_RQ_MVB_DST_RDY,

            UP_MFB_DATA        => DMA_RQ_MFB_DATA,
            UP_MFB_SOF         => DMA_RQ_MFB_SOF,
            UP_MFB_EOF         => DMA_RQ_MFB_EOF,
            UP_MFB_SOF_POS     => DMA_RQ_MFB_SOF_POS,
            UP_MFB_EOF_POS     => DMA_RQ_MFB_EOF_POS,
            UP_MFB_SRC_RDY     => DMA_RQ_MFB_SRC_RDY,
            UP_MFB_DST_RDY     => DMA_RQ_MFB_DST_RDY,

            DOWN_MVB_DATA      => DMA_RC_MVB_DATA,
            DOWN_MVB_VLD       => DMA_RC_MVB_VLD,
            DOWN_MVB_SRC_RDY   => DMA_RC_MVB_SRC_RDY,
            DOWN_MVB_DST_RDY   => DMA_RC_MVB_DST_RDY,

            DOWN_MFB_DATA      => DMA_RC_MFB_DATA,
            DOWN_MFB_SOF       => DMA_RC_MFB_SOF,
            DOWN_MFB_EOF       => DMA_RC_MFB_EOF,
            DOWN_MFB_SOF_POS   => DMA_RC_MFB_SOF_POS,
            DOWN_MFB_EOF_POS   => DMA_RC_MFB_EOF_POS,
            DOWN_MFB_SRC_RDY   => DMA_RC_MFB_SRC_RDY,
            DOWN_MFB_DST_RDY   => DMA_RC_MFB_DST_RDY,

            RCB_SIZE           => CTL_RCB_SIZE,

            TAG_ASSIGN         => RQ_TAG_ASSIGN,
            TAG_ASSIGN_VLD     => RQ_TAG_ASSIGN_VLD
        );
    else generate
        -- DMA_RQ/RC_* clocked at PCIE_CLK
        DMA_RQ_MVB_DST_RDY <= (others => '0');

        DMA_RC_MVB_DATA    <= (others => (others => '0'));
        DMA_RC_MVB_VLD     <= (others => (others => '0'));
        DMA_RC_MVB_SRC_RDY <= (others => '0');

        PCIE_RQ_MFB_DATA      <= DMA_RQ_MFB_DATA(0);
        PCIE_RQ_MFB_META      <= DMA_RQ_MFB_META(0); 
        PCIE_RQ_MFB_SOF       <= DMA_RQ_MFB_SOF(0);
        PCIE_RQ_MFB_EOF       <= DMA_RQ_MFB_EOF(0);
        PCIE_RQ_MFB_SOF_POS   <= DMA_RQ_MFB_SOF_POS(0);
        PCIE_RQ_MFB_EOF_POS   <= DMA_RQ_MFB_EOF_POS(0);
        PCIE_RQ_MFB_SRC_RDY   <= DMA_RQ_MFB_SRC_RDY(0);
        DMA_RQ_MFB_DST_RDY(0) <= PCIE_RQ_MFB_DST_RDY;

        DMA_RC_MFB_DATA(0)    <= PCIE_RC_MFB_DATA;
        DMA_RC_MFB_META(0)    <= PCIE_RC_MFB_META; 
        DMA_RC_MFB_SOF(0)     <= PCIE_RC_MFB_SOF;
        DMA_RC_MFB_EOF(0)     <= PCIE_RC_MFB_EOF;
        DMA_RC_MFB_SOF_POS(0) <= PCIE_RC_MFB_SOF_POS;
        DMA_RC_MFB_EOF_POS(0) <= PCIE_RC_MFB_EOF_POS;
        DMA_RC_MFB_SRC_RDY(0) <= PCIE_RC_MFB_SRC_RDY;
        PCIE_RC_MFB_DST_RDY   <= DMA_RC_MFB_DST_RDY(0);
    end generate;

    -- =========================================================================
    -- DMA-BAR SPLITTER/MERGER
    -- =========================================================================

    dma_bar_g: if DMA_BAR_ENABLE generate
        -- first 64b BAR (BAR0) is for MI access (MTC)
        -- second 64b BAR (BAR2) is for special DMA access (DMA Calypte)

        pcie_cq_mfb_meta_arr <= slv_array_deser(PCIE_CQ_MFB_META,CQ_MFB_REGIONS);
        pcie_cq_mfb_data_arr <= slv_array_deser(PCIE_CQ_MFB_DATA,CQ_MFB_REGIONS);

        cq_mfb_sel_g: for i in 0 to CQ_MFB_REGIONS-1 generate
            bar_index_g: if (DEVICE="ULTRASCALE") generate
                -- BAR index is in AXI header
                pcie_cq_mfb_bar(i) <= pcie_cq_mfb_data_arr(i)(114 downto 112);
            else generate -- Intel FPGA (R-Tile, P-Tile)
                pcie_cq_mfb_bar(i) <= pcie_cq_mfb_meta_arr(i)(PCIE_CQ_META_BAR);
            end generate;
            pcie_cq_mfb_sel(i) <= '1' when (unsigned(pcie_cq_mfb_bar(i)) = 2) else '0';
        end generate;

        cq_splitter_i : entity work.MFB_SPLITTER_SIMPLE
        generic map(
            REGIONS     => CQ_MFB_REGIONS,
            REGION_SIZE => CQ_MFB_REGION_SIZE,
            BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
            ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
            META_WIDTH  => PCIE_CQ_META_WIDTH
        )
        port map(
            CLK             => PCIE_CLK,
            RST             => PCIE_RESET(3),
    
            RX_MFB_SEL      => pcie_cq_mfb_sel,
            RX_MFB_DATA     => PCIE_CQ_MFB_DATA,
            RX_MFB_META     => PCIE_CQ_MFB_META,
            RX_MFB_SOF      => PCIE_CQ_MFB_SOF,
            RX_MFB_EOF      => PCIE_CQ_MFB_EOF,
            RX_MFB_SOF_POS  => PCIE_CQ_MFB_SOF_POS,
            RX_MFB_EOF_POS  => PCIE_CQ_MFB_EOF_POS,
            RX_MFB_SRC_RDY  => PCIE_CQ_MFB_SRC_RDY,
            RX_MFB_DST_RDY  => PCIE_CQ_MFB_DST_RDY,
    
            TX0_MFB_DATA    => mtc_fifo_mfb_data,
            TX0_MFB_META    => mtc_fifo_mfb_meta,
            TX0_MFB_SOF     => mtc_fifo_mfb_sof,
            TX0_MFB_EOF     => mtc_fifo_mfb_eof,
            TX0_MFB_SOF_POS => mtc_fifo_mfb_sof_pos,
            TX0_MFB_EOF_POS => mtc_fifo_mfb_eof_pos,
            TX0_MFB_SRC_RDY => mtc_fifo_mfb_src_rdy,
            TX0_MFB_DST_RDY => mtc_fifo_mfb_dst_rdy,
     
            TX1_MFB_DATA    => DMA_CQ_MFB_DATA(0),
            TX1_MFB_META    => DMA_CQ_MFB_META(0),
            TX1_MFB_SOF     => DMA_CQ_MFB_SOF(0),
            TX1_MFB_EOF     => DMA_CQ_MFB_EOF(0),
            TX1_MFB_SOF_POS => DMA_CQ_MFB_SOF_POS(0),
            TX1_MFB_EOF_POS => DMA_CQ_MFB_EOF_POS(0),
            TX1_MFB_SRC_RDY => DMA_CQ_MFB_SRC_RDY(0),
            TX1_MFB_DST_RDY => DMA_CQ_MFB_DST_RDY(0)
        );

        cc_merger_i : entity work.MFB_MERGER_SIMPLE
        generic map(
            REGIONS     => CC_MFB_REGIONS,
            REGION_SIZE => CC_MFB_REGION_SIZE,
            BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
            ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
            META_WIDTH  => PCIE_CC_META_WIDTH,
            MASKING_EN  => False,
            CNT_MAX     => CC_MFB_MERGER_CNT_MAX
        )
        port map(
            CLK             => PCIE_CLK,
            RST             => PCIE_RESET(4),
    
            RX_MFB0_DATA    => mtc_cc_mfb_data,
            RX_MFB0_META    => mtc_cc_mfb_meta,
            RX_MFB0_SOF     => mtc_cc_mfb_sof,
            RX_MFB0_EOF     => mtc_cc_mfb_eof,
            RX_MFB0_SOF_POS => mtc_cc_mfb_sof_pos,
            RX_MFB0_EOF_POS => mtc_cc_mfb_eof_pos,
            RX_MFB0_SRC_RDY => mtc_cc_mfb_src_rdy,
            RX_MFB0_DST_RDY => mtc_cc_mfb_dst_rdy,
    
            RX_MFB1_DATA    => DMA_CC_MFB_DATA(0),
            RX_MFB1_META    => DMA_CC_MFB_META(0),
            RX_MFB1_SOF     => DMA_CC_MFB_SOF(0),
            RX_MFB1_EOF     => DMA_CC_MFB_EOF(0),
            RX_MFB1_SOF_POS => DMA_CC_MFB_SOF_POS(0),
            RX_MFB1_EOF_POS => DMA_CC_MFB_EOF_POS(0),
            RX_MFB1_SRC_RDY => DMA_CC_MFB_SRC_RDY(0),
            RX_MFB1_DST_RDY => DMA_CC_MFB_DST_RDY(0),
     
            TX_MFB_DATA     => PCIE_CC_MFB_DATA,
            TX_MFB_META     => PCIE_CC_MFB_META,
            TX_MFB_SOF      => PCIE_CC_MFB_SOF,
            TX_MFB_EOF      => PCIE_CC_MFB_EOF,
            TX_MFB_SOF_POS  => PCIE_CC_MFB_SOF_POS,
            TX_MFB_EOF_POS  => PCIE_CC_MFB_EOF_POS,
            TX_MFB_SRC_RDY  => PCIE_CC_MFB_SRC_RDY,
            TX_MFB_DST_RDY  => PCIE_CC_MFB_DST_RDY
        );
    else generate
        DMA_CQ_MFB_DATA    <= (others => (others => '0'));
        DMA_CQ_MFB_META    <= (others => (others => '0'));
        DMA_CQ_MFB_SOF     <= (others => (others => '0'));
        DMA_CQ_MFB_EOF     <= (others => (others => '0'));
        DMA_CQ_MFB_SOF_POS <= (others => (others => '0'));
        DMA_CQ_MFB_EOF_POS <= (others => (others => '0'));
        DMA_CQ_MFB_SRC_RDY <= (others => '0');
        DMA_CC_MFB_DST_RDY <= (others => '0');

        mtc_fifo_mfb_data     <= PCIE_CQ_MFB_DATA;
        mtc_fifo_mfb_meta     <= PCIE_CQ_MFB_META;
        mtc_fifo_mfb_sof      <= PCIE_CQ_MFB_SOF;
        mtc_fifo_mfb_eof      <= PCIE_CQ_MFB_EOF;
        mtc_fifo_mfb_sof_pos  <= PCIE_CQ_MFB_SOF_POS;
        mtc_fifo_mfb_eof_pos  <= PCIE_CQ_MFB_EOF_POS;
        mtc_fifo_mfb_src_rdy  <= PCIE_CQ_MFB_SRC_RDY;
        PCIE_CQ_MFB_DST_RDY   <= mtc_fifo_mfb_dst_rdy;

        PCIE_CC_MFB_DATA    <= mtc_cc_mfb_data;
        PCIE_CC_MFB_META    <= mtc_cc_mfb_meta;
        PCIE_CC_MFB_SOF     <= mtc_cc_mfb_sof;
        PCIE_CC_MFB_EOF     <= mtc_cc_mfb_eof;
        PCIE_CC_MFB_SOF_POS <= mtc_cc_mfb_sof_pos;
        PCIE_CC_MFB_EOF_POS <= mtc_cc_mfb_eof_pos;
        PCIE_CC_MFB_SRC_RDY <= mtc_cc_mfb_src_rdy;
        mtc_cc_mfb_dst_rdy  <= PCIE_CC_MFB_DST_RDY;
    end generate;

    -- =========================================================================
    -- MI32 CONTROLLER (MTC)
    -- =========================================================================

    process (PCIE_CLK)
    begin
        if (rising_edge(PCIE_CLK)) then
            ctl_max_payload_reg <= CTL_MAX_PAYLOAD;
        end if;
    end process;

    mtc_i : entity work.MTC
    generic map (
        MFB_REGIONS       => CQ_MFB_REGIONS,
        MFB_REGION_SIZE   => CQ_MFB_REGION_SIZE,
        MFB_BLOCK_SIZE    => CQ_MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH    => CQ_MFB_ITEM_WIDTH,

        BAR0_BASE_ADDR    => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR    => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR    => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR    => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR    => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR    => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR => EXP_ROM_BASE_ADDR,
        
        ENDPOINT_TYPE     => ENDPOINT_TYPE,
        DEVICE            => DEVICE
    )
    port map (
        CLK                  => PCIE_CLK,
        RESET                => PCIE_RESET(1),

        CTL_MAX_PAYLOAD_SIZE => ctl_max_payload_reg,
        CTL_BAR_APERTURE     => CTL_BAR_APERTURE,

        CQ_MFB_DATA          => mtc_cq_mfb_data,
        CQ_MFB_META          => mtc_cq_mfb_meta,
        CQ_MFB_SOF           => mtc_cq_mfb_sof,
        CQ_MFB_EOF           => mtc_cq_mfb_eof,
        CQ_MFB_SOF_POS       => mtc_cq_mfb_sof_pos,
        CQ_MFB_EOF_POS       => mtc_cq_mfb_eof_pos,
        CQ_MFB_SRC_RDY       => mtc_cq_mfb_src_rdy,
        CQ_MFB_DST_RDY       => mtc_cq_mfb_dst_rdy,

        CC_MFB_DATA          => mtc_cc_mfb_data,
        CC_MFB_META          => mtc_cc_mfb_meta,
        CC_MFB_SOF           => mtc_cc_mfb_sof,
        CC_MFB_EOF           => mtc_cc_mfb_eof,
        CC_MFB_SOF_POS       => mtc_cc_mfb_sof_pos,
        CC_MFB_EOF_POS       => mtc_cc_mfb_eof_pos,
        CC_MFB_SRC_RDY       => mtc_cc_mfb_src_rdy,
        CC_MFB_DST_RDY       => mtc_cc_mfb_dst_rdy,

        MI_DWR               => mtc_mi_dwr,
        MI_ADDR              => mtc_mi_addr,
        MI_BE                => mtc_mi_be,
        MI_RD                => mtc_mi_rd,
        MI_WR                => mtc_mi_wr,
        MI_DRD               => mtc_mi_drd,
        MI_ARDY              => mtc_mi_ardy,
        MI_DRDY              => mtc_mi_drdy
    );

    mtc_fifo_i : entity work.MFB_FIFOX
        generic map (
            REGIONS             => CQ_MFB_REGIONS,
            REGION_SIZE         => CQ_MFB_REGION_SIZE,
            BLOCK_SIZE          => CQ_MFB_BLOCK_SIZE,
            ITEM_WIDTH          => CQ_MFB_ITEM_WIDTH,

            META_WIDTH          => PCIE_CQ_META_WIDTH,
            FIFO_DEPTH          => 512,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 2,
            ALMOST_EMPTY_OFFSET => 2)
        port map (
            CLK         => PCIE_CLK,
            RST         => PCIE_RESET(1),

            RX_DATA     => mtc_fifo_mfb_data,
            RX_META     => mtc_fifo_mfb_meta,
            RX_SOF_POS  => mtc_fifo_mfb_sof_pos,
            RX_EOF_POS  => mtc_fifo_mfb_eof_pos,
            RX_SOF      => mtc_fifo_mfb_sof,
            RX_EOF      => mtc_fifo_mfb_eof,
            RX_SRC_RDY  => mtc_fifo_mfb_src_rdy,
            RX_DST_RDY  => mtc_fifo_mfb_dst_rdy,

            TX_DATA     => mtc_cq_mfb_data,
            TX_META     => mtc_cq_mfb_meta,
            TX_SOF_POS  => mtc_cq_mfb_sof_pos,
            TX_EOF_POS  => mtc_cq_mfb_eof_pos,
            TX_SOF      => mtc_cq_mfb_sof,
            TX_EOF      => mtc_cq_mfb_eof,
            TX_SRC_RDY  => mtc_cq_mfb_src_rdy,
            TX_DST_RDY  => mtc_cq_mfb_dst_rdy,

            FIFO_STATUS => open,
            FIFO_AFULL  => open,
            FIFO_AEMPTY => open);

    mi_async_i : entity work.MI_ASYNC
    generic map(
        DEVICE => DEVICE
    )
    port map(
        -- Master interface
        CLK_M     => PCIE_CLK,
        RESET_M   => PCIE_RESET(2),
        MI_M_DWR  => mtc_mi_dwr,
        MI_M_ADDR => mtc_mi_addr,
        MI_M_RD   => mtc_mi_rd,
        MI_M_WR   => mtc_mi_wr,
        MI_M_BE   => mtc_mi_be,
        MI_M_DRD  => mtc_mi_drd,
        MI_M_ARDY => mtc_mi_ardy,
        MI_M_DRDY => mtc_mi_drdy,

        -- Slave interface
        CLK_S     => MI_CLK,
        RESET_S   => MI_RESET,
        MI_S_DWR  => mi_sync_dwr,
        MI_S_ADDR => mi_sync_addr,
        MI_S_RD   => mi_sync_rd,
        MI_S_WR   => mi_sync_wr,
        MI_S_BE   => mi_sync_be,
        MI_S_DRD  => mi_sync_drd,
        MI_S_ARDY => mi_sync_ardy,
        MI_S_DRDY => mi_sync_drdy
    );

    mi_pipe_i : entity work.MI_PIPE
    generic map(
        DEVICE      => DEVICE,
        DATA_WIDTH  => 32,
        ADDR_WIDTH  => 32,
        PIPE_TYPE   => "REG",
        USE_OUTREG  => True,
        FAKE_PIPE   => False
    )
    port map(
        -- Common interface
        CLK      => MI_CLK,
        RESET    => MI_RESET,
        
        -- Input MI interface
        IN_DWR   => mi_sync_dwr,
        IN_ADDR  => mi_sync_addr,
        IN_RD    => mi_sync_rd,
        IN_WR    => mi_sync_wr,
        IN_BE    => mi_sync_be,
        IN_DRD   => mi_sync_drd,
        IN_ARDY  => mi_sync_ardy,
        IN_DRDY  => mi_sync_drdy,
        
        -- Output MI interface
        OUT_DWR  => MI_DWR,
        OUT_ADDR => MI_ADDR,
        OUT_RD   => MI_RD,
        OUT_WR   => MI_WR,
        OUT_BE   => MI_BE,
        OUT_DRD  => MI_DRD,
        OUT_ARDY => MI_ARDY,
        OUT_DRDY => MI_DRDY
    );

    -- =========================================================================
    --  DEBUG logic
    -- =========================================================================

    debug_logic_g : if DEBUG_EN generate

        mi_splitter_endpts_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH => 32               ,
            DATA_WIDTH => 32               ,
            PORTS      => DMA_PORTS        ,
            ADDR_BASE  => mi_addr_base_f   ,
            PIPE_OUT   => (others => false),
            DEVICE     => DEVICE
        )
        port map(
            CLK     => MI_CLK,
            RESET   => MI_RESET,

            RX_DWR  => MI_DBG_DWR       ,
            RX_ADDR => MI_DBG_ADDR      ,
            RX_BE   => MI_DBG_BE        ,
            RX_RD   => MI_DBG_RD        ,
            RX_WR   => MI_DBG_WR        ,
            RX_ARDY => MI_DBG_ARDY      ,
            RX_DRD  => MI_DBG_DRD       ,
            RX_DRDY => MI_DBG_DRDY      ,

            TX_DWR  => mi_split_dbg_dwr ,
            TX_ADDR => mi_split_dbg_addr,
            TX_BE   => mi_split_dbg_be  ,
            TX_RD   => mi_split_dbg_rd  ,
            TX_WR   => mi_split_dbg_wr  ,
            TX_ARDY => mi_split_dbg_ardy,
            TX_DRD  => mi_split_dbg_drd ,
            TX_DRDY => mi_split_dbg_drdy
        );

        dma_ports_dbg_g : for dp in 0 to DMA_PORTS-1 generate

            mi_async_dbg_i : entity work.MI_ASYNC
            generic map(
                DEVICE => DEVICE
            )
            port map(
                CLK_M     => MI_CLK               ,
                RESET_M   => MI_RESET             ,
                MI_M_DWR  => mi_split_dbg_dwr (dp),
                MI_M_ADDR => mi_split_dbg_addr(dp),
                MI_M_RD   => mi_split_dbg_rd  (dp),
                MI_M_WR   => mi_split_dbg_wr  (dp),
                MI_M_BE   => mi_split_dbg_be  (dp),
                MI_M_DRD  => mi_split_dbg_drd (dp),
                MI_M_ARDY => mi_split_dbg_ardy(dp),
                MI_M_DRDY => mi_split_dbg_drdy(dp),

                CLK_S     => DMA_CLK              ,
                RESET_S   => DMA_RESET            ,
                MI_S_DWR  => mi_sync_dbg_dwr  (dp),
                MI_S_ADDR => mi_sync_dbg_addr (dp),
                MI_S_RD   => mi_sync_dbg_rd   (dp),
                MI_S_WR   => mi_sync_dbg_wr   (dp),
                MI_S_BE   => mi_sync_dbg_be   (dp),
                MI_S_DRD  => mi_sync_dbg_drd  (dp),
                MI_S_ARDY => mi_sync_dbg_ardy (dp),
                MI_S_DRDY => mi_sync_dbg_drdy (dp)
            );

            -- -----------------------------------
            --  Streaming Debug Master + Probe(s)
            -- -----------------------------------
            debug_master_i : entity work.STREAMING_DEBUG_MASTER
            generic map(
                CONNECTED_PROBES   => DBG_PROBES              ,
                REGIONS            => RQ_MFB_REGIONS          ,
                DEBUG_ENABLED      => true                    ,
                PROBE_ENABLED      => (1 to DBG_PROBES => 'E'),
                COUNTER_WORD       => (1 to DBG_PROBES => 'E'),
                COUNTER_WAIT       => (1 to DBG_PROBES => 'E'),
                COUNTER_DST_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SRC_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SOP        => (1 to DBG_PROBES => 'D'), -- disabled
                COUNTER_EOP        => (1 to DBG_PROBES => 'D'), -- disabled
                BUS_CONTROL        => (1 to DBG_PROBES => 'D'), -- disabled
                PROBE_NAMES        => DBG_PROBE_STR           ,
                DEBUG_REG          => true
            )
            port map(
                CLK           => DMA_CLK,
                RESET         => DMA_RESET,

                MI_DWR        => mi_sync_dbg_dwr (dp),
                MI_ADDR       => mi_sync_dbg_addr(dp),
                MI_RD         => mi_sync_dbg_rd  (dp),
                MI_WR         => mi_sync_dbg_wr  (dp),
                MI_BE         => mi_sync_dbg_be  (dp),
                MI_DRD        => mi_sync_dbg_drd (dp),
                MI_ARDY       => mi_sync_dbg_ardy(dp),
                MI_DRDY       => mi_sync_dbg_drdy(dp),

                DEBUG_BLOCK   => open                ,
                DEBUG_DROP    => open                ,
                DEBUG_SOP     => (others => '0')     ,
                DEBUG_EOP     => (others => '0')     ,
                DEBUG_SRC_RDY => dp_out_src_rdy  (dp),
                DEBUG_DST_RDY => dp_out_dst_rdy  (dp)
            );

            debug_probe_i : entity work.STREAMING_DEBUG_PROBE_MFB
            generic map(
                REGIONS => RQ_MFB_REGIONS
            )
            port map(
                RX_SOF         => (others => '0')          , -- SOP counters are unecessary => disabled in the Master Probe
                RX_EOF         => (others => '0')          , -- EOP counters are unecessary => disabled in the Master Probe
                RX_SRC_RDY     => DMA_RQ_MFB_SRC_RDY(dp)   ,
                RX_DST_RDY     => open                     ,

                TX_SOF         => open                     ,
                TX_EOF         => open                     ,
                TX_SRC_RDY     => open                     ,
                TX_DST_RDY     => DMA_RQ_MFB_DST_RDY(dp)   ,

                DEBUG_BLOCK    => '0'                      ,
                DEBUG_DROP     => '0'                      ,
                DEBUG_SOF      => open                     ,
                DEBUG_EOF      => open                     ,
                DEBUG_SRC_RDY  => dp_out_src_rdy    (dp)(0),
                DEBUG_DST_RDY  => dp_out_dst_rdy    (dp)(0)
            );
        end generate;

    end generate;

end architecture;
