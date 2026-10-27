-- hbm_tester_tb_wrapper.vhd: test-only wrapper of HBM_TESTER with one flat AXI port group per HBM port
-- Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
-- Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
--
-- SPDX-License-Identifier: CERN-OHL-W-2.0

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- cocotbext-axi needs one signal per AXI channel field, so each HBM port gets its own P<n>_AXI_* group. The user
-- HSI ports of HBM_TESTER are idle; the generators are the only traffic source. The 4-bit AXI3 burst lengths are
-- widened to the 8 bits of AXI4 that cocotbext-axi expects.
entity HBM_TESTER_TB_WRAPPER is
    generic (
        PORTS          : natural := 4;
        CNT_WIDTH      : natural := 14;
        AXI_ADDR_WIDTH : natural := 16;
        AXI_DATA_WIDTH : natural := 256;
        AXI_ID_WIDTH   : natural := 6
    );
    port (
        HBM_CLK       : in  std_logic;
        HBM_RESET     : in  std_logic;
        HBM_INIT_DONE : in  std_logic;

        MI_CLK        : in  std_logic;
        MI_RESET      : in  std_logic;
        MI_DWR        : in  std_logic_vector(31 downto 0);
        MI_ADDR       : in  std_logic_vector(31 downto 0);
        MI_BE         : in  std_logic_vector(3 downto 0);
        MI_RD         : in  std_logic;
        MI_WR         : in  std_logic;
        MI_ARDY       : out std_logic;
        MI_DRD        : out std_logic_vector(31 downto 0);
        MI_DRDY       : out std_logic;

        P0_AXI_AWID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P0_AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P0_AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        P0_AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        P0_AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        P0_AXI_AWVALID : out std_logic;
        P0_AXI_AWREADY : in  std_logic;
        P0_AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P0_AXI_WSTRB   : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        P0_AXI_WLAST   : out std_logic;
        P0_AXI_WVALID  : out std_logic;
        P0_AXI_WREADY  : in  std_logic;
        P0_AXI_BID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P0_AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        P0_AXI_BVALID  : in  std_logic;
        P0_AXI_BREADY  : out std_logic;
        P0_AXI_ARID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P0_AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P0_AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        P0_AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        P0_AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        P0_AXI_ARVALID : out std_logic;
        P0_AXI_ARREADY : in  std_logic;
        P0_AXI_RID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P0_AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P0_AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        P0_AXI_RLAST   : in  std_logic;
        P0_AXI_RVALID  : in  std_logic;
        P0_AXI_RREADY  : out std_logic;
        P1_AXI_AWID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P1_AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P1_AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        P1_AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        P1_AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        P1_AXI_AWVALID : out std_logic;
        P1_AXI_AWREADY : in  std_logic;
        P1_AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P1_AXI_WSTRB   : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        P1_AXI_WLAST   : out std_logic;
        P1_AXI_WVALID  : out std_logic;
        P1_AXI_WREADY  : in  std_logic;
        P1_AXI_BID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P1_AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        P1_AXI_BVALID  : in  std_logic;
        P1_AXI_BREADY  : out std_logic;
        P1_AXI_ARID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P1_AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P1_AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        P1_AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        P1_AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        P1_AXI_ARVALID : out std_logic;
        P1_AXI_ARREADY : in  std_logic;
        P1_AXI_RID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P1_AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P1_AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        P1_AXI_RLAST   : in  std_logic;
        P1_AXI_RVALID  : in  std_logic;
        P1_AXI_RREADY  : out std_logic;
        P2_AXI_AWID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P2_AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P2_AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        P2_AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        P2_AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        P2_AXI_AWVALID : out std_logic;
        P2_AXI_AWREADY : in  std_logic;
        P2_AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P2_AXI_WSTRB   : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        P2_AXI_WLAST   : out std_logic;
        P2_AXI_WVALID  : out std_logic;
        P2_AXI_WREADY  : in  std_logic;
        P2_AXI_BID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P2_AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        P2_AXI_BVALID  : in  std_logic;
        P2_AXI_BREADY  : out std_logic;
        P2_AXI_ARID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P2_AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P2_AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        P2_AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        P2_AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        P2_AXI_ARVALID : out std_logic;
        P2_AXI_ARREADY : in  std_logic;
        P2_AXI_RID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P2_AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P2_AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        P2_AXI_RLAST   : in  std_logic;
        P2_AXI_RVALID  : in  std_logic;
        P2_AXI_RREADY  : out std_logic;
        P3_AXI_AWID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P3_AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P3_AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        P3_AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        P3_AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        P3_AXI_AWVALID : out std_logic;
        P3_AXI_AWREADY : in  std_logic;
        P3_AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P3_AXI_WSTRB   : out std_logic_vector(AXI_DATA_WIDTH/8-1 downto 0);
        P3_AXI_WLAST   : out std_logic;
        P3_AXI_WVALID  : out std_logic;
        P3_AXI_WREADY  : in  std_logic;
        P3_AXI_BID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P3_AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        P3_AXI_BVALID  : in  std_logic;
        P3_AXI_BREADY  : out std_logic;
        P3_AXI_ARID    : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P3_AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        P3_AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        P3_AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        P3_AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        P3_AXI_ARVALID : out std_logic;
        P3_AXI_ARREADY : in  std_logic;
        P3_AXI_RID     : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        P3_AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        P3_AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        P3_AXI_RLAST   : in  std_logic;
        P3_AXI_RVALID  : in  std_logic;
        P3_AXI_RREADY  : out std_logic
    );
end entity;

architecture FULL of HBM_TESTER_TB_WRAPPER is

    constant MAX_PORTS : natural := 4;

    signal axi_awid     : slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
    signal axi_awaddr   : slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
    signal axi_awlen    : slv_array_t(PORTS-1 downto 0)(4-1 downto 0);
    signal axi_awsize   : slv_array_t(PORTS-1 downto 0)(3-1 downto 0);
    signal axi_awburst  : slv_array_t(PORTS-1 downto 0)(2-1 downto 0);
    signal axi_awvalid  : std_logic_vector(PORTS-1 downto 0);
    signal axi_awready  : std_logic_vector(PORTS-1 downto 0);
    signal axi_wdata    : slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal axi_wstrb    : slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH/8-1 downto 0);
    signal axi_wlast    : std_logic_vector(PORTS-1 downto 0);
    signal axi_wvalid   : std_logic_vector(PORTS-1 downto 0);
    signal axi_wready   : std_logic_vector(PORTS-1 downto 0);
    signal axi_bid      : slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
    signal axi_bresp    : slv_array_t(PORTS-1 downto 0)(2-1 downto 0);
    signal axi_bvalid   : std_logic_vector(PORTS-1 downto 0);
    signal axi_bready   : std_logic_vector(PORTS-1 downto 0);
    signal axi_arid     : slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
    signal axi_araddr   : slv_array_t(PORTS-1 downto 0)(AXI_ADDR_WIDTH-1 downto 0);
    signal axi_arlen    : slv_array_t(PORTS-1 downto 0)(4-1 downto 0);
    signal axi_arsize   : slv_array_t(PORTS-1 downto 0)(3-1 downto 0);
    signal axi_arburst  : slv_array_t(PORTS-1 downto 0)(2-1 downto 0);
    signal axi_arvalid  : std_logic_vector(PORTS-1 downto 0);
    signal axi_arready  : std_logic_vector(PORTS-1 downto 0);
    signal axi_rid      : slv_array_t(PORTS-1 downto 0)(AXI_ID_WIDTH-1 downto 0);
    signal axi_rdata    : slv_array_t(PORTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal axi_rresp    : slv_array_t(PORTS-1 downto 0)(2-1 downto 0);
    signal axi_rlast    : std_logic_vector(PORTS-1 downto 0);
    signal axi_rvalid   : std_logic_vector(PORTS-1 downto 0);
    signal axi_rready   : std_logic_vector(PORTS-1 downto 0);

begin

    assert PORTS >= 1 and PORTS <= MAX_PORTS
        report "HBM_TESTER_TB_WRAPPER: PORTS must be 1 to 4."
        severity failure;

    hbm_tester_i : entity work.HBM_TESTER
    generic map (
        DEBUG            => true,
        PORTS            => PORTS,
        BL8_MODE         => (others => '1'),
        CNT_WIDTH        => CNT_WIDTH,
        AXI_ADDR_WIDTH   => AXI_ADDR_WIDTH,
        AXI_DATA_WIDTH   => AXI_DATA_WIDTH,
        AXI_BURST_WIDTH  => 2,
        AXI_ID_WIDTH     => AXI_ID_WIDTH,
        AXI_LEN_WIDTH    => 4,
        AXI_SIZE_WIDTH   => 3,
        AXI_RESP_WIDTH   => 2,
        USR_DATA_WIDTH   => AXI_DATA_WIDTH,
        PORT_ADDR_HBIT   => AXI_ADDR_WIDTH,
        BASE_ADDR_OFFSET => 0,
        DEVICE           => "ULTRASCALE"
    )
    port map (
        HBM_CLK           => HBM_CLK,
        HBM_RESET         => HBM_RESET,
        HBM_INIT_DONE     => HBM_INIT_DONE,

        MI_CLK            => MI_CLK,
        MI_RESET          => MI_RESET,
        MI_DWR            => MI_DWR,
        MI_ADDR           => MI_ADDR,
        MI_BE             => MI_BE,
        MI_RD             => MI_RD,
        MI_WR             => MI_WR,
        MI_ARDY           => MI_ARDY,
        MI_DRD            => MI_DRD,
        MI_DRDY           => MI_DRDY,

        WR_ADDR           => (others => (others => '0')),
        WR_DATA           => (others => (others => '0')),
        WR_DATA_LAST      => (others => '0'),
        WR_VALID          => (others => '0'),
        WR_READY          => open,
        WR_RSP_ACK        => open,
        WR_RSP_VALID      => open,
        WR_RSP_READY      => (others => '1'),
        RD_ADDR           => (others => (others => '0')),
        RD_ADDR_VALID     => (others => '0'),
        RD_ADDR_READY     => open,
        RD_DATA           => open,
        RD_DATA_LAST      => open,
        RD_DATA_VALID     => open,
        RD_DATA_READY     => (others => '1'),

        AXI_AWID          => axi_awid,
        AXI_AWADDR        => axi_awaddr,
        AXI_AWLEN         => axi_awlen,
        AXI_AWSIZE        => axi_awsize,
        AXI_AWBURST       => axi_awburst,
        AXI_AWPROT        => open,
        AXI_AWQOS         => open,
        AXI_AWUSER        => open,
        AXI_AWVALID       => axi_awvalid,
        AXI_AWREADY       => axi_awready,
        AXI_WDATA         => axi_wdata,
        AXI_WSTRB         => axi_wstrb,
        AXI_WUSER_DATA    => open,
        AXI_WUSER_STRB    => open,
        AXI_WLAST         => axi_wlast,
        AXI_WVALID        => axi_wvalid,
        AXI_WREADY        => axi_wready,
        AXI_BID           => axi_bid,
        AXI_BRESP         => axi_bresp,
        AXI_BVALID        => axi_bvalid,
        AXI_BREADY        => axi_bready,
        AXI_ARID          => axi_arid,
        AXI_ARADDR        => axi_araddr,
        AXI_ARLEN         => axi_arlen,
        AXI_ARSIZE        => axi_arsize,
        AXI_ARBURST       => axi_arburst,
        AXI_ARPROT        => open,
        AXI_ARQOS         => open,
        AXI_ARUSER        => open,
        AXI_ARVALID       => axi_arvalid,
        AXI_ARREADY       => axi_arready,
        AXI_RID           => axi_rid,
        AXI_RDATA         => axi_rdata,
        AXI_RUSER_DATA    => (others => (others => '0')),
        AXI_RUSER_ERR_DBE => (others => '0'),
        AXI_RRESP         => axi_rresp,
        AXI_RLAST         => axi_rlast,
        AXI_RVALID        => axi_rvalid,
        AXI_RREADY        => axi_rready
    );

    p0_g : if PORTS > 0 generate
        P0_AXI_AWID    <= axi_awid(0);
        P0_AXI_AWADDR  <= axi_awaddr(0);
        P0_AXI_AWLEN   <= "0000" & axi_awlen(0);
        P0_AXI_AWSIZE  <= axi_awsize(0);
        P0_AXI_AWBURST <= axi_awburst(0);
        P0_AXI_AWVALID <= axi_awvalid(0);
        axi_awready(0) <= P0_AXI_AWREADY;
        P0_AXI_WDATA   <= axi_wdata(0);
        P0_AXI_WSTRB   <= axi_wstrb(0);
        P0_AXI_WLAST   <= axi_wlast(0);
        P0_AXI_WVALID  <= axi_wvalid(0);
        axi_wready(0)  <= P0_AXI_WREADY;
        axi_bid(0)     <= P0_AXI_BID;
        axi_bresp(0)   <= P0_AXI_BRESP;
        axi_bvalid(0)  <= P0_AXI_BVALID;
        P0_AXI_BREADY  <= axi_bready(0);
        P0_AXI_ARID    <= axi_arid(0);
        P0_AXI_ARADDR  <= axi_araddr(0);
        P0_AXI_ARLEN   <= "0000" & axi_arlen(0);
        P0_AXI_ARSIZE  <= axi_arsize(0);
        P0_AXI_ARBURST <= axi_arburst(0);
        P0_AXI_ARVALID <= axi_arvalid(0);
        axi_arready(0) <= P0_AXI_ARREADY;
        axi_rid(0)     <= P0_AXI_RID;
        axi_rdata(0)   <= P0_AXI_RDATA;
        axi_rresp(0)   <= P0_AXI_RRESP;
        axi_rlast(0)   <= P0_AXI_RLAST;
        axi_rvalid(0)  <= P0_AXI_RVALID;
        P0_AXI_RREADY  <= axi_rready(0);
    else generate
        P0_AXI_AWID    <= (others => '0');
        P0_AXI_AWADDR  <= (others => '0');
        P0_AXI_AWLEN   <= (others => '0');
        P0_AXI_AWSIZE  <= (others => '0');
        P0_AXI_AWBURST <= (others => '0');
        P0_AXI_AWVALID <= '0';
        P0_AXI_WDATA   <= (others => '0');
        P0_AXI_WSTRB   <= (others => '0');
        P0_AXI_WLAST   <= '0';
        P0_AXI_WVALID  <= '0';
        P0_AXI_BREADY  <= '0';
        P0_AXI_ARID    <= (others => '0');
        P0_AXI_ARADDR  <= (others => '0');
        P0_AXI_ARLEN   <= (others => '0');
        P0_AXI_ARSIZE  <= (others => '0');
        P0_AXI_ARBURST <= (others => '0');
        P0_AXI_ARVALID <= '0';
        P0_AXI_RREADY  <= '0';
    end generate;

    p1_g : if PORTS > 1 generate
        P1_AXI_AWID    <= axi_awid(1);
        P1_AXI_AWADDR  <= axi_awaddr(1);
        P1_AXI_AWLEN   <= "0000" & axi_awlen(1);
        P1_AXI_AWSIZE  <= axi_awsize(1);
        P1_AXI_AWBURST <= axi_awburst(1);
        P1_AXI_AWVALID <= axi_awvalid(1);
        axi_awready(1) <= P1_AXI_AWREADY;
        P1_AXI_WDATA   <= axi_wdata(1);
        P1_AXI_WSTRB   <= axi_wstrb(1);
        P1_AXI_WLAST   <= axi_wlast(1);
        P1_AXI_WVALID  <= axi_wvalid(1);
        axi_wready(1)  <= P1_AXI_WREADY;
        axi_bid(1)     <= P1_AXI_BID;
        axi_bresp(1)   <= P1_AXI_BRESP;
        axi_bvalid(1)  <= P1_AXI_BVALID;
        P1_AXI_BREADY  <= axi_bready(1);
        P1_AXI_ARID    <= axi_arid(1);
        P1_AXI_ARADDR  <= axi_araddr(1);
        P1_AXI_ARLEN   <= "0000" & axi_arlen(1);
        P1_AXI_ARSIZE  <= axi_arsize(1);
        P1_AXI_ARBURST <= axi_arburst(1);
        P1_AXI_ARVALID <= axi_arvalid(1);
        axi_arready(1) <= P1_AXI_ARREADY;
        axi_rid(1)     <= P1_AXI_RID;
        axi_rdata(1)   <= P1_AXI_RDATA;
        axi_rresp(1)   <= P1_AXI_RRESP;
        axi_rlast(1)   <= P1_AXI_RLAST;
        axi_rvalid(1)  <= P1_AXI_RVALID;
        P1_AXI_RREADY  <= axi_rready(1);
    else generate
        P1_AXI_AWID    <= (others => '0');
        P1_AXI_AWADDR  <= (others => '0');
        P1_AXI_AWLEN   <= (others => '0');
        P1_AXI_AWSIZE  <= (others => '0');
        P1_AXI_AWBURST <= (others => '0');
        P1_AXI_AWVALID <= '0';
        P1_AXI_WDATA   <= (others => '0');
        P1_AXI_WSTRB   <= (others => '0');
        P1_AXI_WLAST   <= '0';
        P1_AXI_WVALID  <= '0';
        P1_AXI_BREADY  <= '0';
        P1_AXI_ARID    <= (others => '0');
        P1_AXI_ARADDR  <= (others => '0');
        P1_AXI_ARLEN   <= (others => '0');
        P1_AXI_ARSIZE  <= (others => '0');
        P1_AXI_ARBURST <= (others => '0');
        P1_AXI_ARVALID <= '0';
        P1_AXI_RREADY  <= '0';
    end generate;

    p2_g : if PORTS > 2 generate
        P2_AXI_AWID    <= axi_awid(2);
        P2_AXI_AWADDR  <= axi_awaddr(2);
        P2_AXI_AWLEN   <= "0000" & axi_awlen(2);
        P2_AXI_AWSIZE  <= axi_awsize(2);
        P2_AXI_AWBURST <= axi_awburst(2);
        P2_AXI_AWVALID <= axi_awvalid(2);
        axi_awready(2) <= P2_AXI_AWREADY;
        P2_AXI_WDATA   <= axi_wdata(2);
        P2_AXI_WSTRB   <= axi_wstrb(2);
        P2_AXI_WLAST   <= axi_wlast(2);
        P2_AXI_WVALID  <= axi_wvalid(2);
        axi_wready(2)  <= P2_AXI_WREADY;
        axi_bid(2)     <= P2_AXI_BID;
        axi_bresp(2)   <= P2_AXI_BRESP;
        axi_bvalid(2)  <= P2_AXI_BVALID;
        P2_AXI_BREADY  <= axi_bready(2);
        P2_AXI_ARID    <= axi_arid(2);
        P2_AXI_ARADDR  <= axi_araddr(2);
        P2_AXI_ARLEN   <= "0000" & axi_arlen(2);
        P2_AXI_ARSIZE  <= axi_arsize(2);
        P2_AXI_ARBURST <= axi_arburst(2);
        P2_AXI_ARVALID <= axi_arvalid(2);
        axi_arready(2) <= P2_AXI_ARREADY;
        axi_rid(2)     <= P2_AXI_RID;
        axi_rdata(2)   <= P2_AXI_RDATA;
        axi_rresp(2)   <= P2_AXI_RRESP;
        axi_rlast(2)   <= P2_AXI_RLAST;
        axi_rvalid(2)  <= P2_AXI_RVALID;
        P2_AXI_RREADY  <= axi_rready(2);
    else generate
        P2_AXI_AWID    <= (others => '0');
        P2_AXI_AWADDR  <= (others => '0');
        P2_AXI_AWLEN   <= (others => '0');
        P2_AXI_AWSIZE  <= (others => '0');
        P2_AXI_AWBURST <= (others => '0');
        P2_AXI_AWVALID <= '0';
        P2_AXI_WDATA   <= (others => '0');
        P2_AXI_WSTRB   <= (others => '0');
        P2_AXI_WLAST   <= '0';
        P2_AXI_WVALID  <= '0';
        P2_AXI_BREADY  <= '0';
        P2_AXI_ARID    <= (others => '0');
        P2_AXI_ARADDR  <= (others => '0');
        P2_AXI_ARLEN   <= (others => '0');
        P2_AXI_ARSIZE  <= (others => '0');
        P2_AXI_ARBURST <= (others => '0');
        P2_AXI_ARVALID <= '0';
        P2_AXI_RREADY  <= '0';
    end generate;

    p3_g : if PORTS > 3 generate
        P3_AXI_AWID    <= axi_awid(3);
        P3_AXI_AWADDR  <= axi_awaddr(3);
        P3_AXI_AWLEN   <= "0000" & axi_awlen(3);
        P3_AXI_AWSIZE  <= axi_awsize(3);
        P3_AXI_AWBURST <= axi_awburst(3);
        P3_AXI_AWVALID <= axi_awvalid(3);
        axi_awready(3) <= P3_AXI_AWREADY;
        P3_AXI_WDATA   <= axi_wdata(3);
        P3_AXI_WSTRB   <= axi_wstrb(3);
        P3_AXI_WLAST   <= axi_wlast(3);
        P3_AXI_WVALID  <= axi_wvalid(3);
        axi_wready(3)  <= P3_AXI_WREADY;
        axi_bid(3)     <= P3_AXI_BID;
        axi_bresp(3)   <= P3_AXI_BRESP;
        axi_bvalid(3)  <= P3_AXI_BVALID;
        P3_AXI_BREADY  <= axi_bready(3);
        P3_AXI_ARID    <= axi_arid(3);
        P3_AXI_ARADDR  <= axi_araddr(3);
        P3_AXI_ARLEN   <= "0000" & axi_arlen(3);
        P3_AXI_ARSIZE  <= axi_arsize(3);
        P3_AXI_ARBURST <= axi_arburst(3);
        P3_AXI_ARVALID <= axi_arvalid(3);
        axi_arready(3) <= P3_AXI_ARREADY;
        axi_rid(3)     <= P3_AXI_RID;
        axi_rdata(3)   <= P3_AXI_RDATA;
        axi_rresp(3)   <= P3_AXI_RRESP;
        axi_rlast(3)   <= P3_AXI_RLAST;
        axi_rvalid(3)  <= P3_AXI_RVALID;
        P3_AXI_RREADY  <= axi_rready(3);
    else generate
        P3_AXI_AWID    <= (others => '0');
        P3_AXI_AWADDR  <= (others => '0');
        P3_AXI_AWLEN   <= (others => '0');
        P3_AXI_AWSIZE  <= (others => '0');
        P3_AXI_AWBURST <= (others => '0');
        P3_AXI_AWVALID <= '0';
        P3_AXI_WDATA   <= (others => '0');
        P3_AXI_WSTRB   <= (others => '0');
        P3_AXI_WLAST   <= '0';
        P3_AXI_WVALID  <= '0';
        P3_AXI_BREADY  <= '0';
        P3_AXI_ARID    <= (others => '0');
        P3_AXI_ARADDR  <= (others => '0');
        P3_AXI_ARLEN   <= (others => '0');
        P3_AXI_ARSIZE  <= (others => '0');
        P3_AXI_ARBURST <= (others => '0');
        P3_AXI_ARVALID <= '0';
        P3_AXI_RREADY  <= '0';
    end generate;

end architecture;
