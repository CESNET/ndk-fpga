-- pcie_core_versal.vhd: PCIe module for Versal devices (CPM in the CIPS)
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Tomas Fukac <fukac@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ============================================================================
--                                Description
-- ============================================================================

-- This is the specific wrapper around the Xilinx Versal PCIe IP core. The actual
-- Versal PCIe IP core is instantiated outside of this core due to architecture
-- limitations (PCIE is incorporated in the Versal Processing System (CIPS)).
-- PCIE core signals are communicated via the MISC_TOP2PCIE and MISC_PCIE2TOP ports.
--
-- The CPM5 CQ descriptor has no BAR aperture, the MTC and the DMA use fixed apertures instead.
-- Configure the BARs of the IP as on the other cards: BAR0 64 MB (MI, BAR_APERTURE in
-- PCIE_TOP) and BAR2 16 MB (DMA).
--
architecture VERSAL of PCIE_CORE is

    function cfg_check return boolean is
    begin
        assert not XVC_ENABLE
            report "PCIE_CORE (VERSAL): XVC is not supported, set VIRTUAL_DEBUG_ENABLE to false."
            severity failure;
        -- The AXI user widths below are known only for these configurations.
        assert (ENDPOINT_MODE = 0 and (PCIE_GEN = 3 or PCIE_GEN = 4))
            or (ENDPOINT_MODE = 1 and PCIE_GEN = 5)
            report "PCIE_CORE (VERSAL): Use Gen3x16, Gen4x16 (ENDPOINT_MODE=0) " &
                   "or Gen5x8x8 (ENDPOINT_MODE=1)."
            severity failure;
        return true;
    end function;

    constant CFG_CHECKED       : boolean := cfg_check;

    constant VSEC_BASE_ADDRESS : natural := 16#E00#;

    constant PCIE_HIPS         : natural := PCIE_ENDPOINTS;
    constant AXI_DATA_WIDTH    : natural := CQ_MFB_REGIONS*256;
    -- Gen3x16 has the 512b interfaces, Gen4x16 and Gen5x8x8 the 1024b ones (see cfg_check)
    constant AXI_CQUSER_WIDTH  : natural := tsel(PCIE_GEN = 3, 231, 465);
    constant AXI_CCUSER_WIDTH  : natural := tsel(PCIE_GEN = 3,  81, 165);
    constant AXI_RQUSER_WIDTH  : natural := tsel(PCIE_GEN = 3, 183, 373);
    constant AXI_RCUSER_WIDTH  : natural := tsel(PCIE_GEN = 3, 161, 337);

    package pcie_misc_versal is new work.pcie_misc_versal_template generic map (
            AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
            AXI_CQUSER_WIDTH => AXI_CQUSER_WIDTH,
            AXI_CCUSER_WIDTH => AXI_CCUSER_WIDTH,
            AXI_RQUSER_WIDTH => AXI_RQUSER_WIDTH,
            AXI_RCUSER_WIDTH => AXI_RCUSER_WIDTH
        );

    signal pcie_hip_clk : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_hip_rst : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_clk     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_rcb_status      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_max_payload     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal cfg_max_read_req    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal cfg_phy_link_status : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal user_lnk_up         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_ext_int_read       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_int_write      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_int_register   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_int_function   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_int_write_data : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_int_write_be   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_int_read_data  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_int_read_dv    : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cq_axi_data  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cq_axi_user  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CQUSER_WIDTH-1 downto 0);
    signal pcie_cq_axi_last  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_keep  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cq_axi_valid : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_ready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_data  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cc_axi_user  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CCUSER_WIDTH-1 downto 0);
    signal pcie_cc_axi_last  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_keep  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cc_axi_valid : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_ready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_data  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rq_axi_user  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RQUSER_WIDTH-1 downto 0);
    signal pcie_rq_axi_last  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_keep  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rq_axi_valid : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_ready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_data  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rc_axi_user  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RCUSER_WIDTH-1 downto 0);
    signal pcie_rc_axi_last  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_keep  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rc_axi_valid : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_ready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal s_axis_rq_tready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal s_axis_cc_tready : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal dbg_credits_ph  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_pd  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal dbg_credits_nph : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_npd : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);

begin

    assert (PCIE_ENDPOINTS = 1 or PCIE_ENDPOINTS = 2)
        report "PCIE_CORE (VERSAL): Only values 1 and 2 are supported for parameter PCIE_ENDPOINTS!"
        severity failure;

    assert DEVICE = "VERSAL"
        report "PCIE_CORE (VERSAL): Only VERSAL device is supported!"
        severity failure;

    assert MISC_TOP2PCIE_WIDTH = pcie_misc_versal.width_out
        report "PCIE_CORE (VERSAL): Invalid width of signal MISC_TOP2PCIE! " &
               "Expected: " & integer'image(pcie_misc_versal.width_out) &
               " actual: " & integer'image(MISC_TOP2PCIE_WIDTH)
        severity failure;

    assert MISC_PCIE2TOP_WIDTH = pcie_misc_versal.width_in
        report "PCIE_CORE (VERSAL): Invalid width of signal MISC_PCIE2TOP! " &
               "Expected: " & integer'image(pcie_misc_versal.width_in) &
               " actual: " & integer'image(MISC_PCIE2TOP_WIDTH)
        severity failure;

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_hip_g : for i in 0 to PCIE_HIPS-1 generate
        signal misc_pcie_out            : pcie_misc_versal.t_misc_pcie_out;
        signal misc_pcie_in             : pcie_misc_versal.t_misc_pcie_in;
    begin
        -- Connection from CIPS on toplevel
        misc_pcie_out    <= pcie_misc_versal.unpack(misc_pcie_out, MISC_TOP2PCIE(i));
        -- Connection to CIPS on toplevel
        MISC_PCIE2TOP(i) <= pcie_misc_versal.pack(misc_pcie_in);

        pcie_rq_axi_ready(i) <= s_axis_rq_tready(i);
        pcie_cc_axi_ready(i) <= s_axis_cc_tready(i);

        pcie_clk(i) <= pcie_hip_clk(i);

        misc_pcie_in.S_AXIS_RQ_TDATA         <= pcie_rq_axi_data(i);
        misc_pcie_in.S_AXIS_RQ_TKEEP         <= pcie_rq_axi_keep(i);
        misc_pcie_in.S_AXIS_RQ_TLAST         <= pcie_rq_axi_last(i);
        misc_pcie_in.S_AXIS_RQ_TUSER         <= pcie_rq_axi_user(i);
        misc_pcie_in.S_AXIS_RQ_TVALID        <= pcie_rq_axi_valid(i);
        misc_pcie_in.M_AXIS_RC_TREADY        <= pcie_rc_axi_ready(i);
        misc_pcie_in.M_AXIS_CQ_TREADY        <= pcie_cq_axi_ready(i);
        misc_pcie_in.S_AXIS_CC_TDATA         <= pcie_cc_axi_data(i);
        misc_pcie_in.S_AXIS_CC_TKEEP         <= pcie_cc_axi_keep(i);
        misc_pcie_in.S_AXIS_CC_TLAST         <= pcie_cc_axi_last(i);
        misc_pcie_in.S_AXIS_CC_TUSER         <= pcie_cc_axi_user(i);
        misc_pcie_in.S_AXIS_CC_TVALID        <= pcie_cc_axi_valid(i);
        misc_pcie_in.CFG_EXT_READ_DATA       <= cfg_ext_int_read_data(i);
        misc_pcie_in.CFG_EXT_READ_DATA_VALID <= cfg_ext_int_read_dv(i);

        pcie_hip_clk(i)                 <= misc_pcie_out.USER_CLK;
        pcie_hip_rst(i)                 <= misc_pcie_out.USER_RESET;
        user_lnk_up(i)                  <= misc_pcie_out.USER_LNK_UP;
        s_axis_rq_tready(i)             <= misc_pcie_out.S_AXIS_RQ_TREADY;
        pcie_rc_axi_data(i)             <= misc_pcie_out.M_AXIS_RC_TDATA;
        pcie_rc_axi_keep(i)             <= misc_pcie_out.M_AXIS_RC_TKEEP;
        pcie_rc_axi_last(i)             <= misc_pcie_out.M_AXIS_RC_TLAST;
        pcie_rc_axi_user(i)             <= misc_pcie_out.M_AXIS_RC_TUSER;
        pcie_rc_axi_valid(i)            <= misc_pcie_out.M_AXIS_RC_TVALID;
        pcie_cq_axi_data(i)             <= misc_pcie_out.M_AXIS_CQ_TDATA;
        pcie_cq_axi_keep(i)             <= misc_pcie_out.M_AXIS_CQ_TKEEP;
        pcie_cq_axi_last(i)             <= misc_pcie_out.M_AXIS_CQ_TLAST;
        pcie_cq_axi_user(i)             <= misc_pcie_out.M_AXIS_CQ_TUSER;
        pcie_cq_axi_valid(i)            <= misc_pcie_out.M_AXIS_CQ_TVALID;
        s_axis_cc_tready(i)             <= misc_pcie_out.S_AXIS_CC_TREADY;
        cfg_phy_link_status(i)          <= misc_pcie_out.CFG_STATUS_PHY_LINK_STATUS;
        cfg_max_payload(i)              <= misc_pcie_out.CFG_STATUS_MAX_PAYLOAD;
        cfg_max_read_req(i)             <= misc_pcie_out.CFG_STATUS_MAX_READ_REQ;
        cfg_rcb_status(i)               <= misc_pcie_out.CFG_STATUS_RCB_STATUS;
        dbg_credits_ph (i)              <= misc_pcie_out.CFG_FC_PH;
        dbg_credits_pd (i)              <= misc_pcie_out.CFG_FC_PD;
        dbg_credits_nph(i)              <= misc_pcie_out.CFG_FC_NPH;
        dbg_credits_npd(i)              <= misc_pcie_out.CFG_FC_NPD;
        cfg_ext_int_read(i)             <= misc_pcie_out.CFG_EXT_READ_RECEIVED;
        cfg_ext_int_write(i)            <= misc_pcie_out.CFG_EXT_WRITE_RECEIVED;
        cfg_ext_int_register(i)         <= misc_pcie_out.CFG_EXT_REGISTER_NUMBER;
        cfg_ext_int_function(i)         <= misc_pcie_out.CFG_EXT_FUNCTION_NUMBER(7 downto 0);
        cfg_ext_int_write_data(i)       <= misc_pcie_out.CFG_EXT_WRITE_DATA;
        cfg_ext_int_write_be(i)         <= misc_pcie_out.CFG_EXT_WRITE_BYTE_ENABLE;
    end generate;

    -- =========================================================================
    --  PCIE ADAPTER, RESET, CONFIGURATION REGISTERS AND DEVICE TREE
    -- =========================================================================

    axi_common_i : entity work.PCIE_CORE_AXI_COMMON
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
        PCIE_ENDPOINTS     => PCIE_ENDPOINTS,
        AXI_DATA_WIDTH     => AXI_DATA_WIDTH,
        AXI_CQUSER_WIDTH   => AXI_CQUSER_WIDTH,
        AXI_CCUSER_WIDTH   => AXI_CCUSER_WIDTH,
        AXI_RQUSER_WIDTH   => AXI_RQUSER_WIDTH,
        AXI_RCUSER_WIDTH   => AXI_RCUSER_WIDTH,
        VSEC_BASE_ADDRESS  => VSEC_BASE_ADDRESS,
        DTB_NEXT_POINTER   => 0,
        -- the configuration extension interface crosses the device from the CIPS
        CFG_EXT_REG        => true,
        -- registers the 1024b RC and RQ paths (Gen4x16, Gen5x8x8) for timing
        AXI_PIPE_EN        => (PCIE_GEN > 3),
        XVC_ENABLE         => false,
        CARD_ID_WIDTH      => CARD_ID_WIDTH,
        RESET_WIDTH        => RESET_WIDTH,
        DEVICE             => DEVICE
    )
    port map (
        PCIE_CLK            => pcie_clk,
        PCIE_HIP_RESET      => pcie_hip_rst,
        PCIE_HIP_LINK_UP    => user_lnk_up,

        CQ_AXI_DATA         => pcie_cq_axi_data,
        CQ_AXI_USER         => pcie_cq_axi_user,
        CQ_AXI_LAST         => pcie_cq_axi_last,
        CQ_AXI_KEEP         => pcie_cq_axi_keep,
        CQ_AXI_VALID        => pcie_cq_axi_valid,
        CQ_AXI_READY        => pcie_cq_axi_ready,

        RC_AXI_DATA         => pcie_rc_axi_data,
        RC_AXI_USER         => pcie_rc_axi_user,
        RC_AXI_LAST         => pcie_rc_axi_last,
        RC_AXI_KEEP         => pcie_rc_axi_keep,
        RC_AXI_VALID        => pcie_rc_axi_valid,
        RC_AXI_READY        => pcie_rc_axi_ready,

        CC_AXI_DATA         => pcie_cc_axi_data,
        CC_AXI_USER         => pcie_cc_axi_user,
        CC_AXI_LAST         => pcie_cc_axi_last,
        CC_AXI_KEEP         => pcie_cc_axi_keep,
        CC_AXI_VALID        => pcie_cc_axi_valid,
        CC_AXI_READY        => pcie_cc_axi_ready,

        RQ_AXI_DATA         => pcie_rq_axi_data,
        RQ_AXI_USER         => pcie_rq_axi_user,
        RQ_AXI_LAST         => pcie_rq_axi_last,
        RQ_AXI_KEEP         => pcie_rq_axi_keep,
        RQ_AXI_VALID        => pcie_rq_axi_valid,
        RQ_AXI_READY        => pcie_rq_axi_ready,

        CFG_PHY_LINK_STATUS => cfg_phy_link_status,
        CFG_MAX_PAYLOAD     => cfg_max_payload,
        CFG_MAX_READ_REQ    => cfg_max_read_req,
        CFG_RCB_STATUS      => cfg_rcb_status,

        CFG_EXT_READ        => cfg_ext_int_read,
        CFG_EXT_WRITE       => cfg_ext_int_write,
        CFG_EXT_REGISTER    => cfg_ext_int_register,
        CFG_EXT_FUNCTION    => cfg_ext_int_function,
        CFG_EXT_WRITE_DATA  => cfg_ext_int_write_data,
        CFG_EXT_WRITE_BE    => cfg_ext_int_write_be,
        CFG_EXT_READ_DATA   => cfg_ext_int_read_data,
        CFG_EXT_READ_DV     => cfg_ext_int_read_dv,

        PCIE_USER_CLK       => PCIE_USER_CLK,
        PCIE_USER_RESET     => PCIE_USER_RESET,

        RQ_MFB_DATA         => RQ_MFB_DATA,
        RQ_MFB_META         => RQ_MFB_META,
        RQ_MFB_SOF          => RQ_MFB_SOF,
        RQ_MFB_EOF          => RQ_MFB_EOF,
        RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS,
        RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS,
        RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY,
        RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY,

        RC_MFB_DATA         => RC_MFB_DATA,
        RC_MFB_META         => RC_MFB_META,
        RC_MFB_SOF          => RC_MFB_SOF,
        RC_MFB_EOF          => RC_MFB_EOF,
        RC_MFB_SOF_POS      => RC_MFB_SOF_POS,
        RC_MFB_EOF_POS      => RC_MFB_EOF_POS,
        RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY,
        RC_MFB_DST_RDY      => RC_MFB_DST_RDY,

        CQ_MFB_DATA         => CQ_MFB_DATA,
        CQ_MFB_META         => CQ_MFB_META,
        CQ_MFB_SOF          => CQ_MFB_SOF,
        CQ_MFB_EOF          => CQ_MFB_EOF,
        CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS,
        CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS,
        CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY,
        CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY,

        CC_MFB_DATA         => CC_MFB_DATA,
        CC_MFB_META         => CC_MFB_META,
        CC_MFB_SOF          => CC_MFB_SOF,
        CC_MFB_EOF          => CC_MFB_EOF,
        CC_MFB_SOF_POS      => CC_MFB_SOF_POS,
        CC_MFB_EOF_POS      => CC_MFB_EOF_POS,
        CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY,
        CC_MFB_DST_RDY      => CC_MFB_DST_RDY,

        PCIE_LINK_UP        => PCIE_LINK_UP,
        PCIE_MPS            => PCIE_MPS,
        PCIE_MRRS           => PCIE_MRRS,
        PCIE_EXT_TAG_EN     => PCIE_EXT_TAG_EN,
        PCIE_10B_TAG_REQ_EN => PCIE_10B_TAG_REQ_EN,
        PCIE_RCB_SIZE       => PCIE_RCB_SIZE,
        CARD_ID             => CARD_ID
    );

    -- =========================================================================
    --  DEBUG logic
    -- =========================================================================

    debug_i : entity work.PCIE_CORE_DEBUG
    generic map (
        PCIE_ENDPOINTS => PCIE_ENDPOINTS,
        DBG_CRDT_PH_W  => 8,
        DBG_CRDT_NPH_W => 8,
        DBG_CRDT_PD_W  => 12,
        DBG_CRDT_NPD_W => 12,
        DBG_ENABLE     => DBG_ENABLE,
        MI_WIDTH       => MI_WIDTH,
        DEVICE         => DEVICE
    )
    port map (
        PCIE_CLK            => pcie_hip_clk,
        PCIE_RESET          => pcie_hip_rst,

        DBG_UP_SRC_RDY      => pcie_rq_axi_valid,
        DBG_UP_DST_RDY      => pcie_rq_axi_ready,
        DBG_DW_SRC_RDY      => pcie_rc_axi_valid,
        DBG_DW_DST_RDY      => pcie_rc_axi_ready,

        DBG_CREDITS_PH      => dbg_credits_ph,
        DBG_CREDITS_NPH     => dbg_credits_nph,
        DBG_CREDITS_PD      => dbg_credits_pd,
        DBG_CREDITS_NPD     => dbg_credits_npd,

        DBG_CREDITS_PH_VLD  => (others => '1'),
        DBG_CREDITS_NPH_VLD => (others => '1'),
        DBG_CREDITS_PD_VLD  => (others => '1'),
        DBG_CREDITS_NPD_VLD => (others => '1'),

        MI_CLK              => MI_CLK,
        MI_RESET            => MI_RESET,
        MI_DWR              => MI_DWR,
        MI_ADDR             => MI_ADDR,
        MI_BE               => MI_BE,
        MI_RD               => MI_RD,
        MI_WR               => MI_WR,
        MI_ARDY             => MI_ARDY,
        MI_DRD              => MI_DRD,
        MI_DRDY             => MI_DRDY
    );

end architecture;
