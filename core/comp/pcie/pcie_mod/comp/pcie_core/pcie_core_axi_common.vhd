-- pcie_core_axi_common.vhd: Logic shared by the PCIE_CORE architectures for AMD AXI PCIe IPs
-- Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

-- ============================================================================
--                                Description
-- ============================================================================

-- The part of the PCIE_CORE architectures USP and VERSAL that does not
-- depend on how the PCIe IP is connected. For each PCIe endpoint it contains
--
-- * the PCIE_ADAPTER between the AXI interfaces of the IP and the MFB ports,
-- * the synchronization of the user reset,
-- * the configuration status registers,
-- * the PCI Express Extended Capability with the Device Tree (PCI_EXT_CAP) and
--   the optional XVC VSEC on the configuration extension interface of the IP.
--
entity PCIE_CORE_AXI_COMMON is
    generic (
        -- =====================================================================
        -- MFB configuration (see PCIE_CORE)
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
        -- PCIe configuration
        -- =====================================================================
        ENDPOINT_TYPE     : string  := "USP";
        PCIE_ENDPOINTS    : natural := 1;
        -- AXI interfaces of the IP
        AXI_DATA_WIDTH    : natural := CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH;
        AXI_CQUSER_WIDTH  : natural := 183;
        AXI_CCUSER_WIDTH  : natural := 81;
        AXI_RQUSER_WIDTH  : natural := 137;
        AXI_RCUSER_WIDTH  : natural := 161;
        -- Byte address of the Device Tree VSEC in the configuration space
        VSEC_BASE_ADDRESS : natural := 16#480#;
        -- Next capability pointer of the Device Tree VSEC
        DTB_NEXT_POINTER  : natural := 0;
        -- Register the configuration extension interface in both directions
        CFG_EXT_REG       : boolean := false;
        -- Register the RC and RQ AXI interfaces in PCIE_ADAPTER
        AXI_PIPE_EN       : boolean := false;

        -- =====================================================================
        -- Other configuration (see PCIE_CORE)
        -- =====================================================================
        XVC_ENABLE        : boolean := false;
        CARD_ID_WIDTH     : natural := 0;
        RESET_WIDTH       : natural := 8;
        DEVICE            : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- Clock and reset of the IP
        -- =====================================================================
        PCIE_CLK            : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_HIP_RESET      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_HIP_LINK_UP    : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- AXI interfaces of the IP (PCIE_CLK)
        -- =====================================================================
        CQ_AXI_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        CQ_AXI_USER         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CQUSER_WIDTH-1 downto 0);
        CQ_AXI_LAST         : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CQ_AXI_KEEP         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
        CQ_AXI_VALID        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CQ_AXI_READY        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        RC_AXI_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        RC_AXI_USER         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RCUSER_WIDTH-1 downto 0);
        RC_AXI_LAST         : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RC_AXI_KEEP         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
        RC_AXI_VALID        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RC_AXI_READY        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        CC_AXI_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        CC_AXI_USER         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CCUSER_WIDTH-1 downto 0);
        CC_AXI_LAST         : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CC_AXI_KEEP         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
        CC_AXI_VALID        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CC_AXI_READY        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        RQ_AXI_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
        RQ_AXI_USER         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RQUSER_WIDTH-1 downto 0);
        RQ_AXI_LAST         : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RQ_AXI_KEEP         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
        RQ_AXI_VALID        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RQ_AXI_READY        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- Configuration status of the IP (PCIE_CLK)
        -- =====================================================================
        CFG_PHY_LINK_STATUS : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
        CFG_MAX_PAYLOAD     : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
        CFG_MAX_READ_REQ    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
        CFG_RCB_STATUS      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- Configuration extension interface of the IP (PCIE_CLK)
        -- =====================================================================
        CFG_EXT_READ        : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CFG_EXT_WRITE       : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CFG_EXT_REGISTER    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
        CFG_EXT_FUNCTION    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
        CFG_EXT_WRITE_DATA  : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
        CFG_EXT_WRITE_BE    : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
        CFG_EXT_READ_DATA   : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
        CFG_EXT_READ_DV     : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- Ports of PCIE_CORE, see there
        -- =====================================================================
        PCIE_USER_CLK       : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_USER_RESET     : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH-1 downto 0);

        RQ_MFB_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        RQ_MFB_META         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
        RQ_MFB_SOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_EOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_SOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        RQ_MFB_EOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        RQ_MFB_SRC_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RQ_MFB_DST_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        RC_MFB_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        RC_MFB_META         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
        RC_MFB_SOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_EOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_SOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        RC_MFB_EOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        RC_MFB_SRC_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RC_MFB_DST_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        CQ_MFB_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
        CQ_MFB_META         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        CQ_MFB_SOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_EOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_SOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
        CQ_MFB_EOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
        CQ_MFB_SRC_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CQ_MFB_DST_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        CC_MFB_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
        CC_MFB_META         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        CC_MFB_SOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_EOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_SOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
        CC_MFB_EOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
        CC_MFB_SRC_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CC_MFB_DST_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        PCIE_LINK_UP        : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_MPS            : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        PCIE_MRRS           : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3-1 downto 0);
        PCIE_EXT_TAG_EN     : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_10B_TAG_REQ_EN : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_RCB_SIZE       : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CARD_ID             : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CARD_ID_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of PCIE_CORE_AXI_COMMON is

    component xvc_vsec is
        port (
            CLK                                : in    std_logic;
            PCIE3_CFG_EXT_FUNCTION_NUMBER      : in    std_logic_vector(7 downto 0);
            PCIE3_CFG_EXT_READ_DATA            : out   std_logic_vector(31 downto 0);
            PCIE3_CFG_EXT_READ_DATA_VALID      : out   std_logic;
            PCIE3_CFG_EXT_READ_RECEIVED        : in    std_logic;
            PCIE3_CFG_EXT_REGISTER_NUMBER      : in    std_logic_vector(9 downto 0);
            PCIE3_CFG_EXT_WRITE_BYTE_ENABLE    : in    std_logic_vector(3 downto 0);
            PCIE3_CFG_EXT_WRITE_DATA           : in    std_logic_vector(31 downto 0);
            PCIE3_CFG_EXT_WRITE_RECEIVED       : in    std_logic
        );
    end component;

    signal pcie_rst_async : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);

begin

    -- =========================================================================
    --  PCIE ADAPTER
    -- =========================================================================

    pcie_adapter_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        pcie_adapter_i : entity work.PCIE_ADAPTER
        generic map (
            CQ_MFB_REGIONS     => CQ_MFB_REGIONS,
            CQ_MFB_REGION_SIZE => CQ_MFB_REGION_SIZE,
            CQ_MFB_BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
            CQ_MFB_ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
            RC_MFB_REGIONS     => RC_MFB_REGIONS,
            RC_MFB_REGION_SIZE => RC_MFB_REGION_SIZE,
            RC_MFB_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
            RC_MFB_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,
            CC_MFB_REGIONS     => CC_MFB_REGIONS,
            CC_MFB_REGION_SIZE => CC_MFB_REGION_SIZE,
            CC_MFB_BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
            CC_MFB_ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
            RQ_MFB_REGIONS     => RQ_MFB_REGIONS,
            RQ_MFB_REGION_SIZE => RQ_MFB_REGION_SIZE,
            RQ_MFB_BLOCK_SIZE  => RQ_MFB_BLOCK_SIZE,
            RQ_MFB_ITEM_WIDTH  => RQ_MFB_ITEM_WIDTH,
            ENDPOINT_TYPE      => ENDPOINT_TYPE,
            DEVICE             => DEVICE,
            AXI_DATA_WIDTH     => AXI_DATA_WIDTH,
            AXI_CQUSER_WIDTH   => AXI_CQUSER_WIDTH,
            AXI_CCUSER_WIDTH   => AXI_CCUSER_WIDTH,
            AXI_RQUSER_WIDTH   => AXI_RQUSER_WIDTH,
            AXI_RCUSER_WIDTH   => AXI_RCUSER_WIDTH,
            AXI_STRADDLING     => false,
            AXI_PIPE_EN        => AXI_PIPE_EN
        )
        port map (
            PCIE_CLK            => PCIE_CLK(i),
            PCIE_RESET          => pcie_rst(i)(0),

            AVST_DOWN_DATA      => (others => '0'),
            AVST_DOWN_HDR       => (others => '0'),
            AVST_DOWN_PREFIX    => (others => '0'),
            AVST_DOWN_SOP       => (others => '0'),
            AVST_DOWN_EOP       => (others => '0'),
            AVST_DOWN_EMPTY     => (others => '0'),
            AVST_DOWN_BAR_RANGE => (others => '0'),
            AVST_DOWN_VALID     => (others => '0'),
            AVST_DOWN_READY     => open,

            AVST_UP_DATA        => open,
            AVST_UP_HDR         => open,
            AVST_UP_PREFIX      => open,
            AVST_UP_SOP         => open,
            AVST_UP_EOP         => open,
            AVST_UP_ERROR       => open,
            AVST_UP_VALID       => open,
            AVST_UP_READY       => '0',

            CRDT_DOWN_INIT_DONE => '0',
            CRDT_DOWN_UPDATE    => open,
            CRDT_DOWN_CNT_PH    => open,
            CRDT_DOWN_CNT_NPH   => open,
            CRDT_DOWN_CNT_CPLH  => open,
            CRDT_DOWN_CNT_PD    => open,
            CRDT_DOWN_CNT_NPD   => open,
            CRDT_DOWN_CNT_CPLD  => open,

            CRDT_UP_INIT_DONE   => '0',
            CRDT_UP_UPDATE      => (others => '0'),
            CRDT_UP_CNT_PH      => (others => '0'),
            CRDT_UP_CNT_NPH     => (others => '0'),
            CRDT_UP_CNT_CPLH    => (others => '0'),
            CRDT_UP_CNT_PD      => (others => '0'),
            CRDT_UP_CNT_NPD     => (others => '0'),
            CRDT_UP_CNT_CPLD    => (others => '0'),

            CQ_AXI_DATA         => CQ_AXI_DATA(i),
            CQ_AXI_USER         => CQ_AXI_USER(i),
            CQ_AXI_LAST         => CQ_AXI_LAST(i),
            CQ_AXI_KEEP         => CQ_AXI_KEEP(i),
            CQ_AXI_VALID        => CQ_AXI_VALID(i),
            CQ_AXI_READY        => CQ_AXI_READY(i),

            RC_AXI_DATA         => RC_AXI_DATA(i),
            RC_AXI_USER         => RC_AXI_USER(i),
            RC_AXI_LAST         => RC_AXI_LAST(i),
            RC_AXI_KEEP         => RC_AXI_KEEP(i),
            RC_AXI_VALID        => RC_AXI_VALID(i),
            RC_AXI_READY        => RC_AXI_READY(i),

            CC_AXI_DATA         => CC_AXI_DATA(i),
            CC_AXI_USER         => CC_AXI_USER(i),
            CC_AXI_LAST         => CC_AXI_LAST(i),
            CC_AXI_KEEP         => CC_AXI_KEEP(i),
            CC_AXI_VALID        => CC_AXI_VALID(i),
            CC_AXI_READY        => CC_AXI_READY(i),

            RQ_AXI_DATA         => RQ_AXI_DATA(i),
            RQ_AXI_USER         => RQ_AXI_USER(i),
            RQ_AXI_LAST         => RQ_AXI_LAST(i),
            RQ_AXI_KEEP         => RQ_AXI_KEEP(i),
            RQ_AXI_VALID        => RQ_AXI_VALID(i),
            RQ_AXI_READY        => RQ_AXI_READY(i),

            CQ_MFB_DATA         => CQ_MFB_DATA(i),
            CQ_MFB_META         => CQ_MFB_META(i),
            CQ_MFB_SOF          => CQ_MFB_SOF(i),
            CQ_MFB_EOF          => CQ_MFB_EOF(i),
            CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS(i),
            CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS(i),
            CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY(i),
            CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY(i),

            RC_MFB_DATA         => RC_MFB_DATA(i),
            RC_MFB_META         => RC_MFB_META(i),
            RC_MFB_SOF          => RC_MFB_SOF(i),
            RC_MFB_EOF          => RC_MFB_EOF(i),
            RC_MFB_SOF_POS      => RC_MFB_SOF_POS(i),
            RC_MFB_EOF_POS      => RC_MFB_EOF_POS(i),
            RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY(i),
            RC_MFB_DST_RDY      => RC_MFB_DST_RDY(i),

            CC_MFB_DATA         => CC_MFB_DATA(i),
            CC_MFB_META         => CC_MFB_META(i),
            CC_MFB_SOF          => CC_MFB_SOF(i),
            CC_MFB_EOF          => CC_MFB_EOF(i),
            CC_MFB_SOF_POS      => CC_MFB_SOF_POS(i),
            CC_MFB_EOF_POS      => CC_MFB_EOF_POS(i),
            CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY(i),
            CC_MFB_DST_RDY      => CC_MFB_DST_RDY(i),

            RQ_MFB_DATA         => RQ_MFB_DATA(i),
            RQ_MFB_META         => RQ_MFB_META(i),
            RQ_MFB_SOF          => RQ_MFB_SOF(i),
            RQ_MFB_EOF          => RQ_MFB_EOF(i),
            RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS(i),
            RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS(i),
            RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY(i),
            RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY(i)
        );
    end generate;

    -- =========================================================================
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_rst_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        pcie_rst_async(i) <= PCIE_HIP_RESET(i) or not PCIE_HIP_LINK_UP(i);

        pcie_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RESET_WIDTH+1
        )
        port map (
            CLK       => PCIE_CLK(i),
            ASYNC_RST => pcie_rst_async(i),
            OUT_RST   => pcie_rst(i)
        );

        PCIE_USER_CLK(i)   <= PCIE_CLK(i);
        PCIE_USER_RESET(i) <= pcie_rst(i)(RESET_WIDTH+1-1 downto 1);
    end generate;

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================

    pcie_cfg_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        process (PCIE_CLK(i))
        begin
            if (rising_edge(PCIE_CLK(i))) then
                PCIE_LINK_UP(i)  <= CFG_PHY_LINK_STATUS(i)(0) and CFG_PHY_LINK_STATUS(i)(1);
                PCIE_RCB_SIZE(i) <= CFG_RCB_STATUS(i);
                PCIE_MRRS(i)     <= CFG_MAX_READ_REQ(i);
                PCIE_MPS(i)      <= '0' & CFG_MAX_PAYLOAD(i);
            end if;
        end process;
        PCIE_EXT_TAG_EN(i)     <= '1';
        PCIE_10B_TAG_REQ_EN(i) <= '0';
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        signal ext_read          : std_logic;
        signal ext_write         : std_logic;
        signal ext_register      : std_logic_vector(9 downto 0);
        signal ext_function      : std_logic_vector(7 downto 0);
        signal ext_write_data    : std_logic_vector(31 downto 0);
        signal ext_write_be      : std_logic_vector(3 downto 0);
        signal ext_read_xvc_data : std_logic_vector(31 downto 0);
        signal ext_read_xvc_dv   : std_logic := '0';
        signal ext_read_dtb_data : std_logic_vector(31 downto 0);
        signal ext_read_dtb_dv   : std_logic := '0';
        signal ext_read_data     : std_logic_vector(31 downto 0);
        signal ext_read_dv       : std_logic;
    begin
        cfg_ext_reg_g : if CFG_EXT_REG generate
            reg_dtb_no_rst_p : process (PCIE_CLK(i))
            begin
                if (rising_edge(PCIE_CLK(i))) then
                    ext_register         <= CFG_EXT_REGISTER(i);
                    ext_function         <= CFG_EXT_FUNCTION(i);
                    ext_write_data       <= CFG_EXT_WRITE_DATA(i);
                    ext_write_be         <= CFG_EXT_WRITE_BE(i);
                    CFG_EXT_READ_DATA(i) <= ext_read_data;
                end if;
            end process;

            reg_dtb_rst_p : process (PCIE_CLK(i))
            begin
                if (rising_edge(PCIE_CLK(i))) then
                    if (pcie_rst(i)(0) = '1') then
                        ext_read           <= '0';
                        ext_write          <= '0';
                        CFG_EXT_READ_DV(i) <= '0';
                    else
                        ext_read           <= CFG_EXT_READ(i);
                        ext_write          <= CFG_EXT_WRITE(i);
                        CFG_EXT_READ_DV(i) <= ext_read_dv;
                    end if;
                end if;
            end process;
        else generate
            ext_read             <= CFG_EXT_READ(i);
            ext_write            <= CFG_EXT_WRITE(i);
            ext_register         <= CFG_EXT_REGISTER(i);
            ext_function         <= CFG_EXT_FUNCTION(i);
            ext_write_data       <= CFG_EXT_WRITE_DATA(i);
            ext_write_be         <= CFG_EXT_WRITE_BE(i);
            CFG_EXT_READ_DATA(i) <= ext_read_data;
            CFG_EXT_READ_DV(i)   <= ext_read_dv;
        end generate;

        -- Device Tree ROM
        pci_ext_cap_i: entity work.PCI_EXT_CAP
        generic map (
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => true,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => DTB_NEXT_POINTER,
            CARD_ID_WIDTH          => CARD_ID_WIDTH,
            CFG_EXT_READ_DV_HOTFIX => false
        )
        port map (
            CLK                    => PCIE_CLK(i),
            CARD_ID                => CARD_ID(i),
            CFG_EXT_READ           => ext_read,
            CFG_EXT_WRITE          => ext_write,
            CFG_EXT_REGISTER       => ext_register,
            CFG_EXT_FUNCTION       => ext_function,
            CFG_EXT_WRITE_DATA     => ext_write_data,
            CFG_EXT_WRITE_BE       => ext_write_be,
            CFG_EXT_READ_DATA      => ext_read_dtb_data,
            CFG_EXT_READ_DV        => ext_read_dtb_dv
        );

        xvc_g: if (XVC_ENABLE) generate
            xvc_i : component xvc_vsec
            port map (
                clk                              => PCIE_CLK(i),
                pcie3_cfg_ext_function_number    => ext_function,
                pcie3_cfg_ext_read_data          => ext_read_xvc_data,
                pcie3_cfg_ext_read_data_valid    => ext_read_xvc_dv,
                pcie3_cfg_ext_read_received      => ext_read,
                pcie3_cfg_ext_register_number    => ext_register,
                pcie3_cfg_ext_write_byte_enable  => ext_write_be,
                pcie3_cfg_ext_write_data         => ext_write_data,
                pcie3_cfg_ext_write_received     => ext_write
            );
        end generate;

        ext_read_dv   <= ext_read_dtb_dv or ext_read_xvc_dv;
        ext_read_data <= ext_read_xvc_data when (ext_read_xvc_dv = '1') else ext_read_dtb_data;
    end generate;

end architecture;
