-- pcie_core_ent.vhd: PCIe module entity
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

entity PCIE_CORE is
    generic(
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
        -- PCIE configuration
        -- =====================================================================
        -- PCIe endpoint type
        ENDPOINT_TYPE    : string := "P_TILE";
        -- PCIe Endpoint (EP) mode: 0=x16, 1=x8x8, 2=x8
        ENDPOINT_MODE    : natural := 0;
        -- Number of PCIe endpoints
        PCIE_ENDPOINTS   : natural := 1;
        -- Number of PCIe clocks per PCIe connector
        PCIE_CLKS        : natural := 1;
        -- Number of PCIe connectors
        PCIE_CONS        : natural := 1;
        -- Number of PCIe lanes in each PCIe connector
        PCIE_LANES       : natural := 16;

        -- =====================================================================
        -- Other configuration
        -- =====================================================================
        -- MI width - for access to debugging probes
        MI_WIDTH         : natural := 32;
        -- Enable of XCV IP, for Xilinx only
        XVC_ENABLE       : boolean := false;
        -- Width of CARD/FPGA ID number
        CARD_ID_WIDTH    : natural := 0;
        -- Reset width for effective reset duplication
        RESET_WIDTH      : natural := 8;
        -- FPGA device
        DEVICE           : string  := "STRATIX10"
    );
    port(
        -- =====================================================================
        -- Input clock and reset
        -- =====================================================================
        -- 100MHz clock from PCIe port
        PCIE_SYSCLK_P       : in  std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        PCIE_SYSCLK_N       : in  std_logic_vector(PCIE_CONS*PCIE_CLKS-1 downto 0);
        -- PCIe reset
        PCIE_SYSRST_N       : in  std_logic_vector(PCIE_CONS-1 downto 0);
        -- nINIT_DONE output of the Reset Release Intel Stratix 10 FPGA IP
        INIT_DONE_N         : in  std_logic;
        
        -- =====================================================================
        -- PCIe serial interface
        -- =====================================================================
        PCIE_RX_P           : in  std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_RX_N           : in  std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_TX_P           : out std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);
        PCIE_TX_N           : out std_logic_vector(PCIE_CONS*PCIE_LANES-1 downto 0);

        -- =====================================================================
        -- Output user PCIe clock and reset
        -- =====================================================================
        PCIE_USER_CLK       : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        PCIE_USER_RESET     : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH-1 downto 0);

        -- =====================================================================
        -- RQ MFB interface (PCIE_USER_CLK)
        --
        -- MFB bus for transferring RQ PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        RQ_MFB_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE*RQ_MFB_ITEM_WIDTH-1 downto 0);
        RQ_MFB_META         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*PCIE_RQ_META_WIDTH-1 downto 0);
        RQ_MFB_SOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_EOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0);
        RQ_MFB_SOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE))-1 downto 0);
        RQ_MFB_EOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*max(1,log2(RQ_MFB_REGION_SIZE*RQ_MFB_BLOCK_SIZE))-1 downto 0);
        RQ_MFB_SRC_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RQ_MFB_DST_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- RC MFB interface (PCIE_USER_CLK)
        --
        -- MFB bus for transferring RC PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        RC_MFB_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE*RC_MFB_ITEM_WIDTH-1 downto 0);
        RC_MFB_META         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*PCIE_RC_META_WIDTH-1 downto 0);
        RC_MFB_SOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_EOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS-1 downto 0);
        RC_MFB_SOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE))-1 downto 0);
        RC_MFB_EOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RC_MFB_REGIONS*max(1,log2(RC_MFB_REGION_SIZE*RC_MFB_BLOCK_SIZE))-1 downto 0);
        RC_MFB_SRC_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        RC_MFB_DST_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- CQ MFB interface (PCIE_USER_CLK)
        --
        -- MFB bus for transferring CQ PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        CQ_MFB_DATA         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE*CQ_MFB_ITEM_WIDTH-1 downto 0);
        CQ_MFB_META         : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*PCIE_CQ_META_WIDTH-1 downto 0);
        CQ_MFB_SOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_EOF          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
        CQ_MFB_SOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE))-1 downto 0);
        CQ_MFB_EOF_POS      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*max(1,log2(CQ_MFB_REGION_SIZE*CQ_MFB_BLOCK_SIZE))-1 downto 0);
        CQ_MFB_SRC_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CQ_MFB_DST_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

        -- =====================================================================
        -- CC MFB interface (PCIE_USER_CLK)
        --
        -- MFB bus for transferring CC PCIe transactions (format according to
        -- the PCIe IP used). Compared to the standard MFB specification, it
        -- does not allow gaps (SRC_RDY=0) inside transactions and requires that
        -- the first transaction in a word starts at byte 0.
        -- =====================================================================
        CC_MFB_DATA         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE*CC_MFB_ITEM_WIDTH-1 downto 0);
        CC_MFB_META         : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*PCIE_CC_META_WIDTH-1 downto 0);
        CC_MFB_SOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_EOF          : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
        CC_MFB_SOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE))-1 downto 0);
        CC_MFB_EOF_POS      : in  slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*max(1,log2(CC_MFB_REGION_SIZE*CC_MFB_BLOCK_SIZE))-1 downto 0);
        CC_MFB_SRC_RDY      : in  std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
        CC_MFB_DST_RDY      : out std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

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
        CARD_ID             : in slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CARD_ID_WIDTH-1 downto 0);

        -- =====================================================================
        -- PCIe tags interface - Xilinx FPGA Only (PCIE_USER_CLK)
        -- =====================================================================
        -- PCIe tag assigned to send transaction
        TAG_ASSIGN          : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS*8-1 downto 0);
        -- Valid bit for assigned tags
        TAG_ASSIGN_VLD      : out slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RQ_MFB_REGIONS-1 downto 0) := (others => (others => '0'));

        -- =====================================================================
        -- MI interface (for debugging)
        -- =====================================================================
        MI_CLK             : in  std_logic;
        MI_RESET           : in  std_logic;
        MI_ADDR            : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR             : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE              : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD              : in  std_logic;
        MI_WR              : in  std_logic;
        MI_DRD             : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY            : out std_logic;
        MI_DRDY            : out std_logic
    );
end entity;
