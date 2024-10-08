-- pcie_top.vhd: Top level of PCIe module
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;
use work.pcie_meta_pack.all;

entity PCIE is
    generic(
        -- =====================================================================
        -- BAR base address configuration
        -- =====================================================================
        BAR0_BASE_ADDR     : std_logic_vector(31 downto 0) := X"01000000";
        BAR1_BASE_ADDR     : std_logic_vector(31 downto 0) := X"02000000";
        BAR2_BASE_ADDR     : std_logic_vector(31 downto 0) := X"03000000";
        BAR3_BASE_ADDR     : std_logic_vector(31 downto 0) := X"04000000";
        BAR4_BASE_ADDR     : std_logic_vector(31 downto 0) := X"05000000";
        BAR5_BASE_ADDR     : std_logic_vector(31 downto 0) := X"06000000";
        EXP_ROM_BASE_ADDR  : std_logic_vector(31 downto 0) := X"0A000000";

        -- =====================================================================
        -- MFB configuration
        -- =====================================================================
        CQ_MFB_REGIONS     : natural := 2;
        CQ_MFB_REGION_SIZE : natural := 1;
        CQ_MFB_BLOCK_SIZE  : natural := 8;
        CQ_MFB_ITEM_WIDTH  : natural := 32;
        RC_MFB_REGIONS     : natural := 2;
        RC_MFB_REGION_SIZE : natural := 1;
        RC_MFB_BLOCK_SIZE  : natural := 8;
        RC_MFB_ITEM_WIDTH  : natural := 32;
        CC_MFB_REGIONS     : natural := 2;
        CC_MFB_REGION_SIZE : natural := 1;
        CC_MFB_BLOCK_SIZE  : natural := 8;
        CC_MFB_ITEM_WIDTH  : natural := 32;
        RQ_MFB_REGIONS     : natural := 2;
        RQ_MFB_REGION_SIZE : natural := 1;
        RQ_MFB_BLOCK_SIZE  : natural := 8;
        RQ_MFB_ITEM_WIDTH  : natural := 32;

        -- =====================================================================
        -- Other configuration
        -- =====================================================================
        -- Total number of DMA_EP, DMA_EP=PCIE_EP or 2*DMA_EP=PCIE_EP
        DMA_PORTS          : natural := 2;
        -- Connected PCIe endpoint type
        PCIE_ENDPOINT_TYPE : string  := "P_TILE";
        -- Connected PCIe endpoint mode: 0=x16, 1=x8x8, 2=x8
        PCIE_ENDPOINT_MODE : natural := 0;
        -- Number of PCIe endpoints
        PCIE_ENDPOINTS     : natural := 1;
        -- Number of PCIe clocks per PCIe connector
        PCIE_CLKS          : natural := 2;
        -- Number of PCIe connectors
        PCIE_CONS          : natural := 1;
        -- Number of PCIe lanes in each PCIe connector
        PCIE_LANES         : natural := 16;
        -- Width of CARD/FPGA ID number
        CARD_ID_WIDTH      : natural := 0;
        -- Disable PTC module and allows direct connection of the DMA module to
        -- the PCIe IP RQ and RC interfaces.
        PTC_DISABLE        : boolean := false;
        -- Enable CQ/CC interface for DMA-BAR, condition DMA_PORTS=PCIE_ENDPOINTS
        DMA_BAR_ENABLE     : boolean := false;
        -- Enable of XCV IP, for Xilinx only
        XVC_ENABLE         : boolean := false;
        -- FPGA device
        DEVICE             : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- CLOCKS AND RESETS
        -- =====================================================================
        -- Clock from PCIe port, 100 MHz
        PCIE_SYSCLK_P       : in  std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        PCIE_SYSCLK_N       : in  std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        -- PCIe reset from PCIe port
        PCIE_SYSRST_N       : in  std_logic_vector(PCIE_CONS-1 downto 0);
        -- nINIT_DONE output of the Reset Release Intel Stratix 10 FPGA IP
        INIT_DONE_N         : in  std_logic;
        -- PCIe user clock and reset
        PCIE_USER_CLK       : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_USER_RESET     : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        -- DMA module clock and reset
        DMA_CLK             : in  std_logic;
        DMA_RESET           : in  std_logic;

        -- =====================================================================
        -- PCIE SERIAL INTERFACE
        -- =====================================================================
        -- Receive data
        PCIE_RX_P           : in  std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_RX_N           : in  std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        -- Transmit data
        PCIE_TX_P           : out std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_TX_N           : out std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);

        -- =====================================================================
        -- Configuration status interface (PCIE_USER_CLK)
        -- =====================================================================
        -- PCIe link up flag per PCIe endpoint
        PCIE_LINK_UP        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        -- PCIe maximum payload size
        PCIE_MPS            : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        -- PCIe maximum read request size
        PCIE_MRRS           : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        -- PCIe extended tag enable (8-bit tag)
        PCIE_EXT_TAG_EN     : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        -- PCIe 10-bit tag requester enable
        PCIE_10B_TAG_REQ_EN : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        -- PCIe RCB size control
        PCIE_RCB_SIZE       : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        -- Card ID / PCIe Device Serial Number
        CARD_ID             : in slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CARD_ID_WIDTH-1 downto 0) := (others => (others => '0'));

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
        DMA_RQ_MFB_DATA     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        DMA_RQ_MFB_META     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
        DMA_RQ_MFB_SOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        DMA_RQ_MFB_EOF      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        DMA_RQ_MFB_SOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        DMA_RQ_MFB_EOF_POS  : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_RQ_MFB_SRC_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RQ_MFB_DST_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);

        DMA_RQ_MVB_DATA     : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
        DMA_RQ_MVB_VLD      : in  slv_array_t(DMA_PORTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        DMA_RQ_MVB_SRC_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RQ_MVB_DST_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);

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
        DMA_RC_MFB_DATA     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        DMA_RC_MFB_META     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
        DMA_RC_MFB_SOF      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        DMA_RC_MFB_EOF      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        DMA_RC_MFB_SOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        DMA_RC_MFB_EOF_POS  : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        DMA_RC_MFB_SRC_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RC_MFB_DST_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);

        DMA_RC_MVB_DATA     : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS*DMA_DOWNHDR_WIDTH-1 downto 0);
        DMA_RC_MVB_VLD      : out slv_array_t(DMA_PORTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        DMA_RC_MVB_SRC_RDY  : out std_logic_vector(DMA_PORTS-1 downto 0);
        DMA_RC_MVB_DST_RDY  : in  std_logic_vector(DMA_PORTS-1 downto 0);

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
        -- PCIE CC MFB interface - DMA-BAR (PCIE_CLK)
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
        -- MI32 interfaces (MI_CLK)
        --
        -- MI - Root of the MI32 bus tree for each PCIe endpoint (connection to the MTC)
        -- MI_DBG - MI interface to PCIe registers (currently only debug registers)
        -- =====================================================================
        MI_CLK              : in  std_logic;
        MI_RESET            : in  std_logic;

        MI_DWR              : out slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(32-1 downto 0);
        MI_ADDR             : out slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(32-1 downto 0);
        MI_BE               : out slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(32/8-1 downto 0);
        MI_RD               : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        MI_WR               : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        MI_DRD              : in  slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(32-1 downto 0);
        MI_ARDY             : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        MI_DRDY             : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        MI_DBG_DWR          : in  std_logic_vector(32-1 downto 0);
        MI_DBG_ADDR         : in  std_logic_vector(32-1 downto 0);
        MI_DBG_BE           : in  std_logic_vector(32/8-1 downto 0);
        MI_DBG_RD           : in  std_logic;
        MI_DBG_WR           : in  std_logic;
        MI_DBG_DRD          : out std_logic_vector(32-1 downto 0);
        MI_DBG_ARDY         : out std_logic;
        MI_DBG_DRDY         : out std_logic
    );
end entity;

architecture FULL of PCIE is


    function mi_addr_base_f return slv_array_t;

    function core_regions_f(MFB_REGIONS : natural) return natural is
        variable pcie_mfb_regions : natural;
    begin
        pcie_mfb_regions := MFB_REGIONS;
        
        -- PTC conversion
        if ((not PTC_DISABLE)) then
            if (PCIE_ENDPOINT_TYPE="P_TILE" and PCIE_ENDPOINT_MODE = 1) then
                -- 256b PTC-DMA stream to 512b PCIe stream 
                pcie_mfb_regions := pcie_mfb_regions/2;
            end if;
            if (PCIE_ENDPOINT_TYPE="R_TILE" and PCIE_ENDPOINT_MODE = 0) then
                -- 512b PTC-DMA stream to 1024b PCIe stream 
                pcie_mfb_regions := pcie_mfb_regions*2;
            end if;
        end if;

        return pcie_mfb_regions;
    end function;

    constant DMA_PORTS_PER_EP    : natural := DMA_PORTS/PCIE_ENDPOINTS;
    constant CORE_RQ_MFB_REGIONS : natural := core_regions_f(RQ_MFB_REGIONS);
    constant CORE_RC_MFB_REGIONS : natural := core_regions_f(RC_MFB_REGIONS);
    constant RESET_WIDTH         : natural := 6;
    constant BAR_APERTURE        : natural := 26;

    -- One PCIe Core and PCIE_ENDPOINTS * PCIe Ctrl
    constant MI_SPLIT_PORTS        : natural := 1 + PCIE_ENDPOINTS;
    -- Address offset of the PCIe Ctrl from the base address of the PCIe Core.
    -- Changes must be also made in the top-level Device Tree (TODO).
    constant PCIE_CTRL_ADDR_OFFSET : natural := 16#100000#;
    -- Address offset of each PCIe Endpoint (each one currently contains one debug probe).
    constant PCIE_ENDPOINT_OFFSET  : natural := 1 * 16#40#;

    function mi_addr_base_f return slv_array_t is
        variable mi_addr_base : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    begin
        mi_addr_base(0) := (others => '0');
        for p in 1 to MI_SPLIT_PORTS-1 loop
            mi_addr_base(p) := std_logic_vector(to_unsigned(PCIE_CTRL_ADDR_OFFSET + (p-1)*DMA_PORTS_PER_EP*PCIE_ENDPOINT_OFFSET, 32));
        end loop;
        return mi_addr_base;
    end function;

    signal pcie_clk                : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_reset              : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH-1 downto 0);

    signal pcie_cfg_mps            : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
    signal pcie_cfg_mrrs           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
    signal pcie_cfg_ext_tag_en     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_10b_tag_req_en : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_rcb_size       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal core_rq_mfb_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
    signal core_rq_mfb_meta        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
    signal core_rq_mfb_sof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS-1 downto 0);
    signal core_rq_mfb_eof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS-1 downto 0);
    signal core_rq_mfb_sof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
    signal core_rq_mfb_eof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal core_rq_mfb_src_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_rq_mfb_dst_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_rc_mfb_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
    signal core_rc_mfb_meta        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
    signal core_rc_mfb_sof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS-1 downto 0);
    signal core_rc_mfb_eof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS-1 downto 0);
    signal core_rc_mfb_sof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
    signal core_rc_mfb_eof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
    signal core_rc_mfb_src_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_rc_mfb_dst_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_cq_mfb_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
    signal core_cq_mfb_meta        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
    signal core_cq_mfb_sof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal core_cq_mfb_eof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal core_cq_mfb_sof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
    signal core_cq_mfb_eof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
    signal core_cq_mfb_src_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_cq_mfb_dst_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_cc_mfb_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
    signal core_cc_mfb_meta        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
    signal core_cc_mfb_sof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal core_cc_mfb_eof         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal core_cc_mfb_sof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
    signal core_cc_mfb_eof_pos     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
    signal core_cc_mfb_src_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_cc_mfb_dst_rdy     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal core_rq_tag_assign      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS*8-1 downto 0);
    signal core_rq_tag_assign_vld  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CORE_RQ_MFB_REGIONS-1 downto 0);

    signal mi_dbg_split_dwr        : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_dbg_split_addr       : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_dbg_split_be         : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32/8-1 downto 0);
    signal mi_dbg_split_rd         : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_dbg_split_wr         : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_dbg_split_ardy       : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);
    signal mi_dbg_split_drd        : slv_array_t     (MI_SPLIT_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_dbg_split_drdy       : std_logic_vector(MI_SPLIT_PORTS-1 downto 0);

begin

    assert (CORE_RQ_MFB_REGIONS /= 0) report "PCIE: Unsupported CORE_RQ_MFB_REGIONS configuration!"
        severity failure;

    assert (CORE_RC_MFB_REGIONS /= 0) report "PCIE: Unsupported CORE_RC_MFB_REGIONS configuration!"
        severity failure;

    -- =========================================================================
    --  PCIE CORE
    -- =========================================================================

    -- The architecture depends on the selected PCIe Hard IP (or used FPGA),
    -- see Modules.tcl of PCIE_CORE.
    pcie_core_i : entity work.PCIE_CORE
    generic map (
        CQ_MFB_REGIONS     => CQ_MFB_REGIONS,
        CQ_MFB_REGION_SIZE => CQ_MFB_REGION_SIZE,
        CQ_MFB_BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
        CQ_MFB_ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
        RC_MFB_REGIONS     => CORE_RC_MFB_REGIONS,
        RC_MFB_REGION_SIZE => RC_MFB_REGION_SIZE,
        RC_MFB_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
        RC_MFB_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,
        CC_MFB_REGIONS     => CC_MFB_REGIONS,
        CC_MFB_REGION_SIZE => CC_MFB_REGION_SIZE,
        CC_MFB_BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
        CC_MFB_ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
        RQ_MFB_REGIONS     => CORE_RQ_MFB_REGIONS,
        RQ_MFB_REGION_SIZE => RQ_MFB_REGION_SIZE,
        RQ_MFB_BLOCK_SIZE  => RQ_MFB_BLOCK_SIZE,
        RQ_MFB_ITEM_WIDTH  => RQ_MFB_ITEM_WIDTH,
        ENDPOINT_TYPE      => PCIE_ENDPOINT_TYPE,
        ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,
        PCIE_ENDPOINTS     => PCIE_ENDPOINTS,
        PCIE_CLKS          => PCIE_CLKS,
        PCIE_CONS          => PCIE_CONS,
        PCIE_LANES         => PCIE_LANES,
        MI_WIDTH           => 32,
        XVC_ENABLE         => XVC_ENABLE,
        CARD_ID_WIDTH      => CARD_ID_WIDTH,
        RESET_WIDTH        => RESET_WIDTH,
        DEVICE             => DEVICE
    )
    port map (
        PCIE_SYSCLK_P       => PCIE_SYSCLK_P,
        PCIE_SYSCLK_N       => PCIE_SYSCLK_N,
        PCIE_SYSRST_N       => PCIE_SYSRST_N,
        INIT_DONE_N         => INIT_DONE_N,
        
        PCIE_RX_P           => PCIE_RX_P,
        PCIE_RX_N           => PCIE_RX_N,
        PCIE_TX_P           => PCIE_TX_P,
        PCIE_TX_N           => PCIE_TX_N,

        PCIE_USER_CLK       => pcie_clk,
        PCIE_USER_RESET     => pcie_reset,

        PCIE_LINK_UP        => PCIE_LINK_UP,
        PCIE_MPS            => pcie_cfg_mps,
        PCIE_MRRS           => pcie_cfg_mrrs,
        PCIE_EXT_TAG_EN     => pcie_cfg_ext_tag_en,
        PCIE_10B_TAG_REQ_EN => pcie_cfg_10b_tag_req_en,
        PCIE_RCB_SIZE       => pcie_cfg_rcb_size,

        CARD_ID             => CARD_ID,

        CQ_MFB_DATA         => core_cq_mfb_data,
        CQ_MFB_META         => core_cq_mfb_meta,
        CQ_MFB_SOF          => core_cq_mfb_sof,
        CQ_MFB_EOF          => core_cq_mfb_eof,
        CQ_MFB_SOF_POS      => core_cq_mfb_sof_pos,
        CQ_MFB_EOF_POS      => core_cq_mfb_eof_pos,
        CQ_MFB_SRC_RDY      => core_cq_mfb_src_rdy,
        CQ_MFB_DST_RDY      => core_cq_mfb_dst_rdy,

        RC_MFB_DATA         => core_rc_mfb_data,
        RC_MFB_META         => core_rc_mfb_meta,
        RC_MFB_SOF          => core_rc_mfb_sof,
        RC_MFB_EOF          => core_rc_mfb_eof,
        RC_MFB_SOF_POS      => core_rc_mfb_sof_pos,
        RC_MFB_EOF_POS      => core_rc_mfb_eof_pos,
        RC_MFB_SRC_RDY      => core_rc_mfb_src_rdy,
        RC_MFB_DST_RDY      => core_rc_mfb_dst_rdy,

        CC_MFB_DATA         => core_cc_mfb_data,
        CC_MFB_META         => core_cc_mfb_meta,
        CC_MFB_SOF          => core_cc_mfb_sof,
        CC_MFB_EOF          => core_cc_mfb_eof,
        CC_MFB_SOF_POS      => core_cc_mfb_sof_pos,
        CC_MFB_EOF_POS      => core_cc_mfb_eof_pos,
        CC_MFB_SRC_RDY      => core_cc_mfb_src_rdy,
        CC_MFB_DST_RDY      => core_cc_mfb_dst_rdy,

        RQ_MFB_DATA         => core_rq_mfb_data,
        RQ_MFB_META         => core_rq_mfb_meta,
        RQ_MFB_SOF          => core_rq_mfb_sof,
        RQ_MFB_EOF          => core_rq_mfb_eof,
        RQ_MFB_SOF_POS      => core_rq_mfb_sof_pos,
        RQ_MFB_EOF_POS      => core_rq_mfb_eof_pos,
        RQ_MFB_SRC_RDY      => core_rq_mfb_src_rdy,
        RQ_MFB_DST_RDY      => core_rq_mfb_dst_rdy,

        TAG_ASSIGN          => core_rq_tag_assign,
        TAG_ASSIGN_VLD      => core_rq_tag_assign_vld,

        MI_CLK              => MI_CLK,
        MI_RESET            => MI_RESET,
        MI_ADDR             => mi_dbg_split_addr(0),
        MI_DWR              => mi_dbg_split_dwr (0),
        MI_BE               => mi_dbg_split_be  (0),
        MI_RD               => mi_dbg_split_rd  (0),
        MI_WR               => mi_dbg_split_wr  (0),
        MI_DRD              => mi_dbg_split_drd (0),
        MI_ARDY             => mi_dbg_split_ardy(0),
        MI_DRDY             => mi_dbg_split_drdy(0)
    );

    PCIE_USER_CLK <= pcie_clk;
    pcie_user_reset_g: for i in 0 to PCIE_ENDPOINTS-1 generate
        PCIE_USER_RESET(i) <= pcie_reset(i)(RESET_WIDTH-1);
    end generate;

    PCIE_MPS            <= pcie_cfg_mps;
    PCIE_MRRS           <= pcie_cfg_mrrs;
    PCIE_EXT_TAG_EN     <= pcie_cfg_ext_tag_en;
    PCIE_10B_TAG_REQ_EN <= pcie_cfg_10b_tag_req_en;
    PCIE_RCB_SIZE       <= pcie_cfg_rcb_size;

    -- =========================================================================
    --  PCIE CONTROLLERS
    -- =========================================================================

    pcie_ctrl_g: for i in 0 to PCIE_ENDPOINTS-1 generate
        subtype DPE is natural range (i+1)*DMA_PORTS_PER_EP-1 downto i*DMA_PORTS_PER_EP;
    begin
        pcie_ctrl_i : entity work.PCIE_CTRL
        generic map (
            BAR0_BASE_ADDR      => BAR0_BASE_ADDR,
            BAR1_BASE_ADDR      => BAR1_BASE_ADDR,
            BAR2_BASE_ADDR      => BAR2_BASE_ADDR,
            BAR3_BASE_ADDR      => BAR3_BASE_ADDR,
            BAR4_BASE_ADDR      => BAR4_BASE_ADDR,
            BAR5_BASE_ADDR      => BAR5_BASE_ADDR,
            EXP_ROM_BASE_ADDR   => EXP_ROM_BASE_ADDR,
            CQ_MFB_REGIONS      => CQ_MFB_REGIONS,
            CQ_MFB_REGION_SIZE  => CQ_MFB_REGION_SIZE,
            CQ_MFB_BLOCK_SIZE   => CQ_MFB_BLOCK_SIZE,
            CQ_MFB_ITEM_WIDTH   => CQ_MFB_ITEM_WIDTH,
            RC_MFB_REGIONS      => CORE_RC_MFB_REGIONS,
            RC_MFB_REGION_SIZE  => RC_MFB_REGION_SIZE,
            RC_MFB_BLOCK_SIZE   => RC_MFB_BLOCK_SIZE,
            RC_MFB_ITEM_WIDTH   => RC_MFB_ITEM_WIDTH,
            RC_MFB_REGIONS_DMA  => RC_MFB_REGIONS,
            CC_MFB_REGIONS      => CC_MFB_REGIONS,
            CC_MFB_REGION_SIZE  => CC_MFB_REGION_SIZE,
            CC_MFB_BLOCK_SIZE   => CC_MFB_BLOCK_SIZE,
            CC_MFB_ITEM_WIDTH   => CC_MFB_ITEM_WIDTH,
            RQ_MFB_REGIONS      => CORE_RQ_MFB_REGIONS,
            RQ_MFB_REGION_SIZE  => RQ_MFB_REGION_SIZE,
            RQ_MFB_BLOCK_SIZE   => RQ_MFB_BLOCK_SIZE,
            RQ_MFB_ITEM_WIDTH   => RQ_MFB_ITEM_WIDTH,
            RQ_MFB_REGIONS_DMA  => RQ_MFB_REGIONS,
            DMA_PORTS           => DMA_PORTS_PER_EP,
            PTC_DISABLE         => PTC_DISABLE,
            DMA_BAR_ENABLE      => DMA_BAR_ENABLE,
            ENDPOINT_TYPE       => PCIE_ENDPOINT_TYPE,
            DEVICE              => DEVICE
        )
        port map (
            PCIE_CLK            => pcie_clk(i),
            PCIE_RESET          => pcie_reset(i)(5-1 downto 0),
            DMA_CLK             => DMA_CLK,
            DMA_RESET           => DMA_RESET,
            MI_CLK              => MI_CLK,
            MI_RESET            => MI_RESET,

            CTL_MAX_PAYLOAD     => pcie_cfg_mps(i),
            CTL_BAR_APERTURE    => std_logic_vector(to_unsigned(BAR_APERTURE,6)),
            CTL_RCB_SIZE        => pcie_cfg_rcb_size(i),

            PCIE_RQ_MFB_DATA    => core_rq_mfb_data(i),
            PCIE_RQ_MFB_META    => core_rq_mfb_meta(i),
            PCIE_RQ_MFB_SOF     => core_rq_mfb_sof(i),
            PCIE_RQ_MFB_EOF     => core_rq_mfb_eof(i),
            PCIE_RQ_MFB_SOF_POS => core_rq_mfb_sof_pos(i),
            PCIE_RQ_MFB_EOF_POS => core_rq_mfb_eof_pos(i),
            PCIE_RQ_MFB_SRC_RDY => core_rq_mfb_src_rdy(i),
            PCIE_RQ_MFB_DST_RDY => core_rq_mfb_dst_rdy(i),

            PCIE_RC_MFB_DATA    => core_rc_mfb_data(i),
            PCIE_RC_MFB_META    => core_rc_mfb_meta(i),
            PCIE_RC_MFB_SOF     => core_rc_mfb_sof(i),
            PCIE_RC_MFB_EOF     => core_rc_mfb_eof(i),
            PCIE_RC_MFB_SOF_POS => core_rc_mfb_sof_pos(i),
            PCIE_RC_MFB_EOF_POS => core_rc_mfb_eof_pos(i),
            PCIE_RC_MFB_SRC_RDY => core_rc_mfb_src_rdy(i),
            PCIE_RC_MFB_DST_RDY => core_rc_mfb_dst_rdy(i),

            PCIE_CQ_MFB_DATA    => core_cq_mfb_data(i),
            PCIE_CQ_MFB_META    => core_cq_mfb_meta(i),
            PCIE_CQ_MFB_SOF     => core_cq_mfb_sof(i),
            PCIE_CQ_MFB_EOF     => core_cq_mfb_eof(i),
            PCIE_CQ_MFB_SOF_POS => core_cq_mfb_sof_pos(i),
            PCIE_CQ_MFB_EOF_POS => core_cq_mfb_eof_pos(i),
            PCIE_CQ_MFB_SRC_RDY => core_cq_mfb_src_rdy(i),
            PCIE_CQ_MFB_DST_RDY => core_cq_mfb_dst_rdy(i),

            PCIE_CC_MFB_DATA    => core_cc_mfb_data(i),
            PCIE_CC_MFB_META    => core_cc_mfb_meta(i),
            PCIE_CC_MFB_SOF     => core_cc_mfb_sof(i),
            PCIE_CC_MFB_EOF     => core_cc_mfb_eof(i),
            PCIE_CC_MFB_SOF_POS => core_cc_mfb_sof_pos(i),
            PCIE_CC_MFB_EOF_POS => core_cc_mfb_eof_pos(i),
            PCIE_CC_MFB_SRC_RDY => core_cc_mfb_src_rdy(i),
            PCIE_CC_MFB_DST_RDY => core_cc_mfb_dst_rdy(i),

            DMA_RQ_MFB_DATA     => DMA_RQ_MFB_DATA(DPE),
            DMA_RQ_MFB_META     => DMA_RQ_MFB_META(DPE),
            DMA_RQ_MFB_SOF      => DMA_RQ_MFB_SOF(DPE),
            DMA_RQ_MFB_EOF      => DMA_RQ_MFB_EOF(DPE),
            DMA_RQ_MFB_SOF_POS  => DMA_RQ_MFB_SOF_POS(DPE),
            DMA_RQ_MFB_EOF_POS  => DMA_RQ_MFB_EOF_POS(DPE),
            DMA_RQ_MFB_SRC_RDY  => DMA_RQ_MFB_SRC_RDY(DPE),
            DMA_RQ_MFB_DST_RDY  => DMA_RQ_MFB_DST_RDY(DPE),

            DMA_RQ_MVB_DATA     => DMA_RQ_MVB_DATA(DPE),
            DMA_RQ_MVB_VLD      => DMA_RQ_MVB_VLD(DPE),
            DMA_RQ_MVB_SRC_RDY  => DMA_RQ_MVB_SRC_RDY(DPE),
            DMA_RQ_MVB_DST_RDY  => DMA_RQ_MVB_DST_RDY(DPE),

            DMA_RC_MFB_DATA     => DMA_RC_MFB_DATA(DPE),
            DMA_RC_MFB_META     => DMA_RC_MFB_META(DPE),
            DMA_RC_MFB_SOF      => DMA_RC_MFB_SOF(DPE),
            DMA_RC_MFB_EOF      => DMA_RC_MFB_EOF(DPE),
            DMA_RC_MFB_SOF_POS  => DMA_RC_MFB_SOF_POS(DPE),
            DMA_RC_MFB_EOF_POS  => DMA_RC_MFB_EOF_POS(DPE),
            DMA_RC_MFB_SRC_RDY  => DMA_RC_MFB_SRC_RDY(DPE),
            DMA_RC_MFB_DST_RDY  => DMA_RC_MFB_DST_RDY(DPE),

            DMA_RC_MVB_DATA     => DMA_RC_MVB_DATA(DPE),
            DMA_RC_MVB_VLD      => DMA_RC_MVB_VLD(DPE),
            DMA_RC_MVB_SRC_RDY  => DMA_RC_MVB_SRC_RDY(DPE),
            DMA_RC_MVB_DST_RDY  => DMA_RC_MVB_DST_RDY(DPE),

            DMA_CQ_MFB_DATA     => DMA_CQ_MFB_DATA(DPE),
            DMA_CQ_MFB_META     => DMA_CQ_MFB_META(DPE),
            DMA_CQ_MFB_SOF      => DMA_CQ_MFB_SOF(DPE),
            DMA_CQ_MFB_EOF      => DMA_CQ_MFB_EOF(DPE),
            DMA_CQ_MFB_SOF_POS  => DMA_CQ_MFB_SOF_POS(DPE),
            DMA_CQ_MFB_EOF_POS  => DMA_CQ_MFB_EOF_POS(DPE),
            DMA_CQ_MFB_SRC_RDY  => DMA_CQ_MFB_SRC_RDY(DPE),
            DMA_CQ_MFB_DST_RDY  => DMA_CQ_MFB_DST_RDY(DPE),

            DMA_CC_MFB_DATA     => DMA_CC_MFB_DATA(DPE),
            DMA_CC_MFB_META     => DMA_CC_MFB_META(DPE),
            DMA_CC_MFB_SOF      => DMA_CC_MFB_SOF(DPE),
            DMA_CC_MFB_EOF      => DMA_CC_MFB_EOF(DPE),
            DMA_CC_MFB_SOF_POS  => DMA_CC_MFB_SOF_POS(DPE),
            DMA_CC_MFB_EOF_POS  => DMA_CC_MFB_EOF_POS(DPE),
            DMA_CC_MFB_SRC_RDY  => DMA_CC_MFB_SRC_RDY(DPE),
            DMA_CC_MFB_DST_RDY  => DMA_CC_MFB_DST_RDY(DPE),

            RQ_TAG_ASSIGN       => core_rq_tag_assign(i),
            RQ_TAG_ASSIGN_VLD   => core_rq_tag_assign_vld(i),

            MI_DWR              => MI_DWR (i),
            MI_ADDR             => MI_ADDR(i),
            MI_BE               => MI_BE  (i),
            MI_RD               => MI_RD  (i),
            MI_WR               => MI_WR  (i),
            MI_DRD              => MI_DRD (i),
            MI_ARDY             => MI_ARDY(i),
            MI_DRDY             => MI_DRDY(i),

            MI_DBG_DWR          => mi_dbg_split_dwr (i+1),
            MI_DBG_ADDR         => mi_dbg_split_addr(i+1),
            MI_DBG_BE           => mi_dbg_split_be  (i+1),
            MI_DBG_RD           => mi_dbg_split_rd  (i+1),
            MI_DBG_WR           => mi_dbg_split_wr  (i+1),
            MI_DBG_DRD          => mi_dbg_split_drd (i+1),
            MI_DBG_ARDY         => mi_dbg_split_ardy(i+1),
            MI_DBG_DRDY         => mi_dbg_split_drdy(i+1)
        );
    end generate;

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH => 32               ,
        DATA_WIDTH => 32               ,
        PORTS      => MI_SPLIT_PORTS   ,
        ADDR_BASE  => mi_addr_base_f   ,
        PIPE_OUT   => (others => false),
        DEVICE     => DEVICE
    )
    port map(
        CLK     => MI_CLK           ,
        RESET   => MI_RESET         ,

        RX_DWR  => MI_DBG_DWR       ,
        RX_ADDR => MI_DBG_ADDR      ,
        RX_BE   => MI_DBG_BE        ,
        RX_RD   => MI_DBG_RD        ,
        RX_WR   => MI_DBG_WR        ,
        RX_ARDY => MI_DBG_ARDY      ,
        RX_DRD  => MI_DBG_DRD       ,
        RX_DRDY => MI_DBG_DRDY      ,

        TX_DWR  => mi_dbg_split_dwr ,
        TX_ADDR => mi_dbg_split_addr,
        TX_BE   => mi_dbg_split_be  ,
        TX_RD   => mi_dbg_split_rd  ,
        TX_WR   => mi_dbg_split_wr  ,
        TX_ARDY => mi_dbg_split_ardy,
        TX_DRD  => mi_dbg_split_drd ,
        TX_DRDY => mi_dbg_split_drdy
    );

end architecture;
