-- pcie_core.vhd: PCIe module entity
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
    generic (
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
        -- PCIe generation number
        PCIE_GEN         : natural := 4;

        -- =====================================================================
        -- Other configuration
        -- =====================================================================
        -- MI width - for access to debugging probes
        MI_WIDTH            : natural := 32;
        -- Width of CARD/FPGA ID number
        CARD_ID_WIDTH       : natural := 0;
        -- Reset width for effective reset duplication
        RESET_WIDTH         : natural := 8;
        -- FPGA device
        DEVICE              : string  := "STRATIX10"
    );
    port (
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
        -- Card ID / PCIe Device Serial Number
        CARD_ID             : in slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CARD_ID_WIDTH-1 downto 0)
    );
end entity;

architecture VERSAL of PCIE_CORE is

    constant VSEC_BASE_ADDRESS : natural := tsel(ENDPOINT_TYPE = "USP_PCIE4C", 16#E80#, 16#480#);
    constant DTB_NEXT_POINTER  : natural := 0;

    constant PCIE_HIPS         : natural := PCIE_ENDPOINTS;
    constant PCIE_IP_LANES     : natural := tsel(ENDPOINT_MODE = 1, PCIE_LANES/2, PCIE_LANES);
    constant AXI_DATA_WIDTH    : natural := CQ_MFB_REGIONS*256;
    constant AXI_CQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 231, 109);
    constant AXI_CCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 81, 33);
    constant AXI_RQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 183, 85);
    constant AXI_RCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 161, 75);

    signal pcie_sysclk_buf          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_sysclk_gt_buf       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_hip_rst             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst_async           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);

    signal cfg_max_payload          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal cfg_max_read_req         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal cfg_phy_link_status      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal user_lnk_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_function         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_dtb_data    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dtb_dv      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CQUSER_WIDTH-1 downto 0);
    signal pcie_cq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CCUSER_WIDTH-1 downto 0);
    signal pcie_cc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RQUSER_WIDTH-1 downto 0);
    signal pcie_rq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RCUSER_WIDTH-1 downto 0);
    signal pcie_rc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    -- attribute mark_debug                 : string;
    -- special signals for debugging
    -- attribute mark_debug of pcie_cq_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_cc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_ready_s : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_rc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_valid : signal is "true";

    -- attribute mark_debug of cfg_phy_link_down        : signal is "true";
    -- attribute mark_debug of cfg_phy_link_status      : signal is "true";
    -- attribute mark_debug of pcie_phy_rdy_out         : signal is "true";
    -- attribute mark_debug of cfg_max_payload          : signal is "true";
    -- attribute mark_debug of cfg_max_read_req         : signal is "true";

    -- attribute mark_debug of cfg_negotiated_width     : signal is "true";
    -- attribute mark_debug of cfg_current_speed        : signal is "true";
    -- attribute mark_debug of cfg_function_status      : signal is "true";
    -- attribute mark_debug of cfg_function_power_state : signal is "true";
    -- attribute mark_debug of cfg_link_power_state     : signal is "true";
    -- attribute mark_debug of cfg_rx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_tx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_ltssm_state          : signal is "true";
    -- attribute mark_debug of cfg_local_error_out      : signal is "true";
    -- attribute mark_debug of cfg_local_error_valid    : signal is "true";

begin
    assert (ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1 or ENDPOINT_MODE = 2)
        report "Versal PCIe Wrapper: Only values 0, 1 and 2 are supported for parameter ENDPOINT_MODE!"
        severity failure;

    assert (PCIE_ENDPOINTS = 1)
        report "Versal PCIe Wrapper: Only values 0 are supported for parameter PCIE_ENDPOINTS!"
        severity failure;

    assert DEVICE = "VERSAL"
        report "Versal PCIe Wrapper: Only VERSAL device is supported!"
        severity failure;

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================
    pcie_clk(i) <= pcie_hip_clk(i);

    vsparkle_cips_i : entity work.vsparkle_cips
    port map (
        PCIE0_GT_0_grx_n   => PCIE_RX_N,
        PCIE0_GT_0_grx_p   => PCIE_RX_P,
        PCIE0_GT_0_gtx_n   => PCIE_RX_N,
        PCIE0_GT_0_gtx_p   => PCIE_RX_P,

        gt_refclk0_0_clk_n => PCIE_SYSCLK_P(0),
        gt_refclk0_0_clk_p => PCIE_SYSCLK_N(0),

        pcie0_cfg_ext_0_read_received     => cfg_ext_read(0),
        pcie0_cfg_ext_0_write_received    => cfg_ext_write(0),
        pcie0_cfg_ext_0_register_number   => cfg_ext_register(0),
        pcie0_cfg_ext_0_function_number   => cfg_ext_function(0),
        pcie0_cfg_ext_0_write_data        => cfg_ext_write_data(0),
        pcie0_cfg_ext_0_write_byte_enable => cfg_ext_write_be(0),
        pcie0_cfg_ext_0_read_data         => cfg_ext_read_data(0),
        pcie0_cfg_ext_0_read_data_valid   => cfg_ext_read_dv(0),

        pcie0_cfg_interrupt_0_intx_vector => (others => '0'),
        pcie0_cfg_interrupt_0_pending     => (others => '0'),
        pcie0_cfg_interrupt_0_sent        => open,

        pcie0_cfg_status_0_10b_tag_requester_enable => open,
        pcie0_cfg_status_0_atomic_requester_enable  => open,
        pcie0_cfg_status_0_bus_number               => open,
        pcie0_cfg_status_0_cq_np_req                => (others => '0'),
        pcie0_cfg_status_0_cq_np_req_count          => open,
        pcie0_cfg_status_0_current_speed            => open,
        pcie0_cfg_status_0_err_cor_out              => open,
        pcie0_cfg_status_0_err_fatal_out            => open,
        pcie0_cfg_status_0_err_nonfatal_out         => open,
        pcie0_cfg_status_0_ext_tag_enable           => open,
        pcie0_cfg_status_0_function_power_state     => open,
        pcie0_cfg_status_0_function_status          => open,
        pcie0_cfg_status_0_link_power_state         => open,
        pcie0_cfg_status_0_local_error_out          => open,
        pcie0_cfg_status_0_local_error_valid        => open,
        pcie0_cfg_status_0_ltssm_state              => open,
        pcie0_cfg_status_0_max_payload              => cfg_max_payload(0),
        pcie0_cfg_status_0_max_read_req             => cfg_max_read_req(0),
        pcie0_cfg_status_0_negotiated_width         => open,
        pcie0_cfg_status_0_per_function_out         => open,
        pcie0_cfg_status_0_per_function_vld         => open,
        pcie0_cfg_status_0_phy_link_down            => open,
        pcie0_cfg_status_0_phy_link_status          => cfg_phy_link_status(0),
        pcie0_cfg_status_0_pl_status_change         => open,
        pcie0_cfg_status_0_rcb_status               => open,
        pcie0_cfg_status_0_rq_seq_num0              => open,
        pcie0_cfg_status_0_rq_seq_num1              => open,
        pcie0_cfg_status_0_rq_seq_num2              => open,
        pcie0_cfg_status_0_rq_seq_num3              => open,
        pcie0_cfg_status_0_rq_seq_num_vld0          => open,
        pcie0_cfg_status_0_rq_seq_num_vld1          => open,
        pcie0_cfg_status_0_rq_seq_num_vld2          => open,
        pcie0_cfg_status_0_rq_seq_num_vld3          => open,
        pcie0_cfg_status_0_rq_tag0                  => open,
        pcie0_cfg_status_0_rq_tag1                  => open,
        pcie0_cfg_status_0_rq_tag2                  => open,
        pcie0_cfg_status_0_rq_tag3                  => open,
        pcie0_cfg_status_0_rq_tag_av                => open,
        pcie0_cfg_status_0_rq_tag_vld0              => open,
        pcie0_cfg_status_0_rq_tag_vld1              => open,
        pcie0_cfg_status_0_rq_tag_vld2              => open,
        pcie0_cfg_status_0_rq_tag_vld3              => open,
        pcie0_cfg_status_0_rx_pm_state              => open,
        pcie0_cfg_status_0_tph_requester_enable     => open,
        pcie0_cfg_status_0_tph_st_mode              => open,
        pcie0_cfg_status_0_tx_pm_state              => open,
        pcie0_cfg_status_0_wrreq_bme_vld            => open,
        pcie0_cfg_status_0_wrreq_flr_vld            => open,
        pcie0_cfg_status_0_wrreq_function_number    => open,
        pcie0_cfg_status_0_wrreq_msi_vld            => open,
        pcie0_cfg_status_0_wrreq_msix_vld           => open,
        pcie0_cfg_status_0_wrreq_out_value          => open,
        pcie0_cfg_status_0_wrreq_vfe_vld            => open,

        pcie0_m_axis_cq_0_tdata  => pcie_cq_axi_data(0),
        pcie0_m_axis_cq_0_tkeep  => pcie_cq_axi_user(0),
        pcie0_m_axis_cq_0_tlast  => pcie_cq_axi_last(0),
        pcie0_m_axis_cq_0_tready => pcie_cq_axi_keep(0),
        pcie0_m_axis_cq_0_tuser  => pcie_cq_axi_valid(0),
        pcie0_m_axis_cq_0_tvalid => pcie_cq_axi_ready(0),

        pcie0_m_axis_rc_0_tdata  => pcie_rc_axi_data(0),
        pcie0_m_axis_rc_0_tkeep  => pcie_rc_axi_user(0),
        pcie0_m_axis_rc_0_tlast  => pcie_rc_axi_last(0),
        pcie0_m_axis_rc_0_tready => pcie_rc_axi_keep(0),
        pcie0_m_axis_rc_0_tuser  => pcie_rc_axi_valid(0),
        pcie0_m_axis_rc_0_tvalid => pcie_rc_axi_ready(0),

        pcie0_s_axis_cc_0_tdata  => pcie_cc_axi_data(0),
        pcie0_s_axis_cc_0_tkeep  => pcie_cc_axi_user(0),
        pcie0_s_axis_cc_0_tlast  => pcie_cc_axi_last(0),
        pcie0_s_axis_cc_0_tready => pcie_cc_axi_keep(0),
        pcie0_s_axis_cc_0_tuser  => pcie_cc_axi_valid(0),
        pcie0_s_axis_cc_0_tvalid => pcie_cc_axi_ready(0),

        pcie0_s_axis_rq_0_tdata  => pcie_rq_axi_last(0),
        pcie0_s_axis_rq_0_tkeep  => pcie_rq_axi_data(0),
        pcie0_s_axis_rq_0_tlast  => pcie_rq_axi_user(0),
        pcie0_s_axis_rq_0_tready => pcie_rq_axi_keep(0),
        pcie0_s_axis_rq_0_tuser  => pcie_rq_axi_ready(0),
        pcie0_s_axis_rq_0_tvalid => pcie_rq_axi_valid(0),

        pcie0_user_clk_0    => pcie_hip_clk,
        pcie0_user_lnk_up_0 => user_lnk_up,
        pcie0_user_reset_0  => pcie_hip_rst 
    );

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

            AXI_CQUSER_WIDTH   => AXI_CQUSER_WIDTH,
            AXI_CCUSER_WIDTH   => AXI_CCUSER_WIDTH,
            AXI_RQUSER_WIDTH   => AXI_RQUSER_WIDTH,
            AXI_RCUSER_WIDTH   => AXI_RCUSER_WIDTH,

            AXI_STRADDLING     => (CQ_MFB_REGIONS = 2) 
        )
        port map (
            PCIE_CLK            => pcie_clk(i),
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

            CQ_AXI_DATA         => pcie_cq_axi_data(i),
            CQ_AXI_USER         => pcie_cq_axi_user(i),
            CQ_AXI_LAST         => pcie_cq_axi_last(i),
            CQ_AXI_KEEP         => pcie_cq_axi_keep(i),
            CQ_AXI_VALID        => pcie_cq_axi_valid(i),
            CQ_AXI_READY        => pcie_cq_axi_ready(i),

            RC_AXI_DATA         => pcie_rc_axi_data(i),
            RC_AXI_USER         => pcie_rc_axi_user(i),
            RC_AXI_LAST         => pcie_rc_axi_last(i),
            RC_AXI_KEEP         => pcie_rc_axi_keep(i),
            RC_AXI_VALID        => pcie_rc_axi_valid(i),
            RC_AXI_READY        => pcie_rc_axi_ready(i),

            CC_AXI_DATA         => pcie_cc_axi_data(i),
            CC_AXI_USER         => pcie_cc_axi_user(i),
            CC_AXI_LAST         => pcie_cc_axi_last(i),
            CC_AXI_KEEP         => pcie_cc_axi_keep(i),
            CC_AXI_VALID        => pcie_cc_axi_valid(i),
            CC_AXI_READY        => pcie_cc_axi_ready(i),

            RQ_AXI_DATA         => pcie_rq_axi_data(i),
            RQ_AXI_USER         => pcie_rq_axi_user(i),
            RQ_AXI_LAST         => pcie_rq_axi_last(i),
            RQ_AXI_KEEP         => pcie_rq_axi_keep(i),
            RQ_AXI_VALID        => pcie_rq_axi_valid(i),
            RQ_AXI_READY        => pcie_rq_axi_ready(i),

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
        pcie_rst_async(i) <= pcie_hip_rst(i) or not user_lnk_up(i);

        pcie_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RESET_WIDTH+1
        )
        port map (
            CLK       => pcie_clk(i),
            ASYNC_RST => pcie_rst_async(i),
            OUT_RST   => pcie_rst(i)
        );

        PCIE_USER_CLK(i)   <= pcie_clk(i);
        PCIE_USER_RESET(i) <= pcie_rst(i)(RESET_WIDTH+1-1 downto 1);
    end generate;

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================
    pcie_cfg_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                PCIE_LINK_UP(i)  <= cfg_phy_link_status(i)(0) and cfg_phy_link_status(i)(1);
                PCIE_MRRS(i)     <= cfg_max_read_req(i);
                PCIE_MPS(i)      <= '0' & cfg_max_payload(i);
            end if;
        end process;
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================
    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        constant DT_EN : boolean := true;
    begin
        -- Device Tree ROM
        pci_ext_cap_i: entity work.PCI_EXT_CAP
        generic map (
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => dt_en,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => DTB_NEXT_POINTER,
            CARD_ID_WIDTH          => CARD_ID_WIDTH,
            CFG_EXT_READ_DV_HOTFIX => false
        )
        port map (
            CLK                    => pcie_clk(i),
            CARD_ID                => CARD_ID(i),
            CFG_EXT_READ           => cfg_ext_read(i),
            CFG_EXT_WRITE          => cfg_ext_write(i),
            CFG_EXT_REGISTER       => cfg_ext_register(i),
            CFG_EXT_FUNCTION       => cfg_ext_function(i),
            CFG_EXT_WRITE_DATA     => cfg_ext_write_data(i),
            CFG_EXT_WRITE_BE       => cfg_ext_write_be(i),
            CFG_EXT_READ_DATA      => cfg_ext_read_dtb_data(i),
            CFG_EXT_READ_DV        => cfg_ext_read_dtb_dv(i)
        );

        cfg_ext_read_dv(i)   <= cfg_ext_read_dtb_dv(i);
        cfg_ext_read_data(i) <= cfg_ext_read_dtb_data(i);
    end generate;
end architecture;
