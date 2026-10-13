-- hbm_fb2cdg1.vhd: Silicom ThunderFjord fb2cdg1 High Bandwidth Memory Interface
-- Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;

-- Wrapper for the NoC based HBM
entity HBM_FB2CDG1 is
generic (
    -- Up to 16 ports are supported, with a capacity of 1 GB each.
    HBM_PORTS           : natural := 16;
    HBM_AXI_ID_WIDTH    : natural := 7;
    HBM_AXI_ADDR_WIDTH  : natural := 44;
    HBM_AXI_LEN_WIDTH   : natural := 8;
    HBM_AXI_SIZE_WIDTH  : natural := 3;
    HBM_AXI_BURST_WIDTH : natural := 2;
    HBM_AXI_DATA_WIDTH  : natural := 256;
    HBM_AXI_RESP_WIDTH  : natural := 2
);
port (
    -- Connect these directly to the top-level pins
    CORE_PLL_REFCLK_CLK             : in std_logic;
    HBM_CATTRIP_VIRTUAL_I_CONDUIT   : in std_logic;
    HBM_TEMP_VIRTUAL_I_CONDUIT      : in std_logic_vector(2 downto 0);
    UIBPLL_REFCLK_CLK               : in std_logic;
    HBM_ONLY_RESET_RESET            : in std_logic;
    NOC_CLK_CTRL_REFCLK_CLK         : in std_logic;

    HBM_CLK         : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_RST         : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_INIT_DONE   : out std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_AWID    : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    HBM_AXI_AWADDR  : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    HBM_AXI_AWLEN   : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    HBM_AXI_AWSIZE  : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    HBM_AXI_AWBURST : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    HBM_AXI_AWVALID : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_AWREADY : out std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_WDATA   : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    HBM_AXI_WSTRB   : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH/8-1 downto 0);
    HBM_AXI_WLAST   : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_WVALID  : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_WREADY  : out std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_BID     : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    HBM_AXI_BRESP   : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    HBM_AXI_BVALID  : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_BREADY  : in  std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_ARID    : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    HBM_AXI_ARADDR  : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    HBM_AXI_ARLEN   : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    HBM_AXI_ARSIZE  : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    HBM_AXI_ARBURST : in  slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    HBM_AXI_ARVALID : in  std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_ARREADY : out std_logic_vector(HBM_PORTS-1 downto 0);

    HBM_AXI_RID     : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    HBM_AXI_RDATA   : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    HBM_AXI_RRESP   : out slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    HBM_AXI_RLAST   : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_RVALID  : out std_logic_vector(HBM_PORTS-1 downto 0);
    HBM_AXI_RREADY  : in  std_logic_vector(HBM_PORTS-1 downto 0)
);
end entity;

architecture FULL of HBM_FB2CDG1 is
    component reset_release_ip is
        port (
            ninit_done : out std_logic   -- ninit_done
        );
    end component reset_release_ip;

    component noc_pll is
        port (
            refclk   : in  std_logic := 'X'; -- clk
            locked   : out std_logic;        -- export
            rst      : in  std_logic := 'X'; -- reset
            outclk_0 : out std_logic;        -- clk
            outclk_1 : out std_logic         -- clk
        );
    end component noc_pll;

    component noc_clk_ctrl is
        port (
            refclk     : in  std_logic := 'X'; -- clk
            pll_lock_o : out std_logic         -- pll_lock_o
        );
    end component noc_clk_ctrl;

    component hbm2e_noc_target is
        port (
            ch0_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch0_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch1_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch1_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch2_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch2_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch3_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch3_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch4_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch4_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch5_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch5_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch6_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch6_u1_wmc_intr   : out std_logic;                                       -- conduit
            ch7_u0_wmc_intr   : out std_logic;                                       -- conduit
            ch7_u1_wmc_intr   : out std_logic;                                       -- conduit
            fabric_clk        : in  std_logic                    := 'X';             -- clk
            hbm_reset_n       : in  std_logic                    := 'X';             -- reset_n
            hbm_reset_in_prog : out std_logic;                                       -- hbm_reset_in_prog
            hbm_cattrip       : out std_logic;                                       -- hbm_cattrip
            hbm_cattrip_i     : in  std_logic                    := 'X';             -- conduit
            hbm_temp          : out std_logic_vector(2 downto 0);                    -- hbm_temp
            hbm_temp_i        : in  std_logic_vector(2 downto 0) := (others => 'X'); -- conduit
            local_cal_success : out std_logic;                                       -- local_cal_success
            local_cal_fail    : out std_logic;                                       -- local_cal_fail
            uibpll_refclk     : in  std_logic                    := 'X'              -- clk
        );
    end component hbm2e_noc_target;

    constant MAX_HBM_PORTS  : natural := 16;

    signal noc_axi_awid_s    : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal noc_axi_awaddr_s  : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    signal noc_axi_awlen_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    signal noc_axi_awsize_s  : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    signal noc_axi_awburst_s : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    signal noc_axi_awvalid_s : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_awready_s : std_logic_vector(MAX_HBM_PORTS-1 downto 0);

    signal noc_axi_wdata_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    signal noc_axi_wstrb_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH/8-1 downto 0);
    signal noc_axi_wlast_s   : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_wvalid_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_wready_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);

    signal noc_axi_bid_s     : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal noc_axi_bresp_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    signal noc_axi_bvalid_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_bready_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);

    signal noc_axi_arid_s    : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal noc_axi_araddr_s  : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    signal noc_axi_arlen_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    signal noc_axi_arsize_s  : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    signal noc_axi_arburst_s : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    signal noc_axi_arvalid_s : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_arready_s : std_logic_vector(MAX_HBM_PORTS-1 downto 0);

    signal noc_axi_rid_s     : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal noc_axi_rdata_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    signal noc_axi_rresp_s   : slv_array_t(MAX_HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    signal noc_axi_rlast_s   : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_rvalid_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);
    signal noc_axi_rready_s  : std_logic_vector(MAX_HBM_PORTS-1 downto 0);

    signal local_cal_success     : std_logic;
    signal local_cal_fail        : std_logic;
    signal hbm_reset_in_prog     : std_logic;
    signal ninit_done            : std_logic;

    signal noc_pll_locked        : std_logic;
    signal fabric_clk            : std_logic;
    signal axi_fabric_clk        : std_logic_vector(MAX_HBM_PORTS - 1 downto 0);
    signal noc_bridge_fabric_clk : std_logic;

    signal hbm_reset_n           : std_logic;
    signal axi_reset_n           : std_logic_vector(MAX_HBM_PORTS - 1 downto 0);
begin

    assert ((HBM_AXI_DATA_WIDTH = 256) or (HBM_AXI_DATA_WIDTH = 512))
        report "HBM_FB2CDG1: Unsupported data width. Only 256 or 512 are supported."
        severity failure;

    assert (HBM_PORTS <= MAX_HBM_PORTS)
        report "HBM_FB2CDG1: The HBM module does not support more than 16 HBM ports."
        severity failure;

    assert (HBM_PORTS > 0)
        report "HBM_FB2CDG1: No HBM ports have been assigned."
        severity failure;

    ninit_done_i: component reset_release_ip
    port map (
        ninit_done => ninit_done
    );

    noc_pll_i: component noc_pll
    port map (
        refclk   => CORE_PLL_REFCLK_CLK,
        locked   => noc_pll_locked,
        rst      => ninit_done,
        outclk_0 => fabric_clk,
        outclk_1 => noc_bridge_fabric_clk
    );

    axi_fabric_clk <= (others => fabric_clk);

    hbm_reset_i: entity work.HBM_FB2CDG1_RESET
    generic map (
        HBM_PORTS => MAX_HBM_PORTS
    )
    port map (
        CLK                  => fabric_clk,
        HBM_ONLY_RESET_RESET => HBM_ONLY_RESET_RESET,

        PLL_LOCKED           => noc_pll_locked,
        HBM_CAL_SUCCESS      => local_cal_success,
        HBM_CAL_FAIL         => local_cal_fail,
        HBM_RESET_IN_PROG    => hbm_reset_in_prog,

        AXI_RESET_N => axi_reset_n,
        HBM_RESET_N => hbm_reset_n
    );

    HBM_CLK         <= (others => fabric_clk);
    HBM_RST         <= not axi_reset_n(HBM_PORTS -1 downto 0);
    HBM_INIT_DONE   <= (others => local_cal_success);

    -- =========================================================================
    -- PLL / Clock Control (Mandatory for NoC)
    -- =========================================================================
    noc_ctrl_i : component noc_clk_ctrl
    port map (
        refclk     => NOC_CLK_CTRL_REFCLK_CLK,
        pll_lock_o => open
    );

    -- =========================================================================
    -- NoC Initiator (Bridging Fabric AXI to Hard NoC)
    -- =========================================================================
    noc_init_i: entity work.NOC_INIT
    generic map (
        -- Currently only 16 is possible
        NOC_PORTS           => MAX_HBM_PORTS,
        NOC_AXI_ID_WIDTH    => HBM_AXI_ID_WIDTH,
        NOC_AXI_ADDR_WIDTH  => HBM_AXI_ADDR_WIDTH,
        NOC_AXI_LEN_WIDTH   => HBM_AXI_LEN_WIDTH,
        NOC_AXI_SIZE_WIDTH  => HBM_AXI_SIZE_WIDTH,
        NOC_AXI_BURST_WIDTH => HBM_AXI_BURST_WIDTH,
        NOC_AXI_DATA_WIDTH  => HBM_AXI_DATA_WIDTH,
        NOC_AXI_RESP_WIDTH  => HBM_AXI_RESP_WIDTH
    )
    port map (
        NOC_BRIDGE_CLK  => noc_bridge_fabric_clk,

        NOC_AXI_CLK     => axi_fabric_clk,
        NOC_AXI_RST_N   => axi_reset_n,

        NOC_AXI_AWID    => noc_axi_awid_s,
        NOC_AXI_AWADDR  => noc_axi_awaddr_s,
        NOC_AXI_AWLEN   => noc_axi_awlen_s,
        NOC_AXI_AWSIZE  => noc_axi_awsize_s,
        NOC_AXI_AWBURST => noc_axi_awburst_s,
        NOC_AXI_AWVALID => noc_axi_awvalid_s,
        NOC_AXI_AWREADY => noc_axi_awready_s,

        NOC_AXI_WDATA   => noc_axi_wdata_s,
        NOC_AXI_WSTRB   => noc_axi_wstrb_s,
        NOC_AXI_WLAST   => noc_axi_wlast_s,
        NOC_AXI_WVALID  => noc_axi_wvalid_s,
        NOC_AXI_WREADY  => noc_axi_wready_s,

        NOC_AXI_BID     => noc_axi_bid_s,
        NOC_AXI_BRESP   => noc_axi_bresp_s,
        NOC_AXI_BVALID  => noc_axi_bvalid_s,
        NOC_AXI_BREADY  => noc_axi_bready_s,

        NOC_AXI_ARID    => noc_axi_arid_s,
        NOC_AXI_ARADDR  => noc_axi_araddr_s,
        NOC_AXI_ARLEN   => noc_axi_arlen_s,
        NOC_AXI_ARSIZE  => noc_axi_arsize_s,
        NOC_AXI_ARBURST => noc_axi_arburst_s,
        NOC_AXI_ARVALID => noc_axi_arvalid_s,
        NOC_AXI_ARREADY => noc_axi_arready_s,

        NOC_AXI_RID     => noc_axi_rid_s,
        NOC_AXI_RDATA   => noc_axi_rdata_s,
        NOC_AXI_RRESP   => noc_axi_rresp_s,
        NOC_AXI_RLAST   => noc_axi_rlast_s,
        NOC_AXI_RVALID  => noc_axi_rvalid_s,
        NOC_AXI_RREADY  => noc_axi_rready_s
    );

    -- =========================================================================
    -- Disconnect unused ports
    -- =========================================================================
    port_connect_g: for i in 0 to HBM_PORTS -1 generate
        noc_axi_awid_s(i)       <= HBM_AXI_AWID(i);
        noc_axi_awaddr_s(i)     <= HBM_AXI_AWADDR(i);
        noc_axi_awlen_s(i)      <= HBM_AXI_AWLEN(i);
        noc_axi_awsize_s(i)     <= HBM_AXI_AWSIZE(i);
        noc_axi_awburst_s(i)    <= HBM_AXI_AWBURST(i);
        noc_axi_awvalid_s(i)    <= HBM_AXI_AWVALID(i);
        HBM_AXI_AWREADY(i)      <= noc_axi_awready_s(i);

        noc_axi_wdata_s(i)      <= HBM_AXI_WDATA(i);
        noc_axi_wstrb_s(i)      <= HBM_AXI_WSTRB(i);
        noc_axi_wlast_s(i)      <= HBM_AXI_WLAST(i);
        noc_axi_wvalid_s(i)     <= HBM_AXI_WVALID(i);
        HBM_AXI_WREADY(i)       <= noc_axi_wready_s(i);

        HBM_AXI_BID(i)          <= noc_axi_bid_s(i);
        HBM_AXI_BRESP(i)        <= noc_axi_bresp_s(i);
        HBM_AXI_BVALID(i)       <= noc_axi_bvalid_s(i);
        noc_axi_bready_s(i)     <= HBM_AXI_BREADY(i);

        noc_axi_arid_s(i)       <= HBM_AXI_ARID(i);
        noc_axi_araddr_s(i)     <= HBM_AXI_ARADDR(i);
        noc_axi_arlen_s(i)      <= HBM_AXI_ARLEN(i);
        noc_axi_arsize_s(i)     <= HBM_AXI_ARSIZE(i);
        noc_axi_arburst_s(i)    <= HBM_AXI_ARBURST(i);
        noc_axi_arvalid_s(i)    <= HBM_AXI_ARVALID(i);
        HBM_AXI_ARREADY(i)      <= noc_axi_arready_s(i);

        HBM_AXI_RID(i)          <= noc_axi_rid_s(i);
        HBM_AXI_RDATA(i)        <= noc_axi_rdata_s(i);
        HBM_AXI_RRESP(i)        <= noc_axi_rresp_s(i);
        HBM_AXI_RLAST(i)        <= noc_axi_rlast_s(i);
        HBM_AXI_RVALID(i)       <= noc_axi_rvalid_s(i);
        noc_axi_rready_s(i)     <= HBM_AXI_RREADY(i);
    end generate;

    port_disconnect_g: for i in HBM_PORTS to MAX_HBM_PORTS - 1 generate
        noc_axi_awid_s(i)    <= (others => '0');
        noc_axi_awaddr_s(i)  <= (others => '0');
        noc_axi_awlen_s(i)   <= (others => '0');
        noc_axi_awsize_s(i)  <= (others => '0');
        noc_axi_awburst_s(i) <= (others => '0');
        noc_axi_awvalid_s(i) <= '0';

        noc_axi_wdata_s(i)   <= (others => '0');
        noc_axi_wstrb_s(i)   <= (others => '0');
        noc_axi_wlast_s(i)   <= '0';
        noc_axi_wvalid_s(i)  <= '0';

        noc_axi_bready_s(i)  <= '0';

        noc_axi_arid_s(i)    <= (others => '0');
        noc_axi_araddr_s(i)  <= (others => '0');
        noc_axi_arlen_s(i)   <= (others => '0');
        noc_axi_arsize_s(i)  <= (others => '0');
        noc_axi_arburst_s(i) <= (others => '0');
        noc_axi_arvalid_s(i) <= '0';

        noc_axi_rready_s(i)  <= '0';
    end generate;

    -- =========================================================================
    -- HBM2e Target (Provides the AXI Targets internally to the Hard NoC)
    -- =========================================================================
    noc_target_i: component hbm2e_noc_target
    port map (
        ch0_u0_wmc_intr   => open,
        ch0_u1_wmc_intr   => open,
        ch1_u0_wmc_intr   => open,
        ch1_u1_wmc_intr   => open,
        ch2_u0_wmc_intr   => open,
        ch2_u1_wmc_intr   => open,
        ch3_u0_wmc_intr   => open,
        ch3_u1_wmc_intr   => open,
        ch4_u0_wmc_intr   => open,
        ch4_u1_wmc_intr   => open,
        ch5_u0_wmc_intr   => open,
        ch5_u1_wmc_intr   => open,
        ch6_u0_wmc_intr   => open,
        ch6_u1_wmc_intr   => open,
        ch7_u0_wmc_intr   => open,
        ch7_u1_wmc_intr   => open,

        fabric_clk        => fabric_clk,
        hbm_reset_n       => hbm_reset_n,
        hbm_reset_in_prog => hbm_reset_in_prog,
        hbm_cattrip       => open,
        hbm_cattrip_i     => HBM_CATTRIP_VIRTUAL_I_CONDUIT,
        hbm_temp          => open,
        hbm_temp_i        => HBM_TEMP_VIRTUAL_I_CONDUIT,
        local_cal_success => local_cal_success,
        local_cal_fail    => local_cal_fail,
        uibpll_refclk     => UIBPLL_REFCLK_CLK
    );

end architecture;
