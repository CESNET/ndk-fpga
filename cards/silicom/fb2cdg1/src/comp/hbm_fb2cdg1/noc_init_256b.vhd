-- noc_init_256b.vhd: 256b NoC initiator
-- Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;

architecture FULL of NOC_INIT is

    component noc_initiator is
        port (
            s0_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s0_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s0_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s0_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s0_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s0_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s0_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s0_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s0_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s0_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s0_axi4_arready       : out std_logic;                                         -- arready
            s0_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s0_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s0_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s0_axi4_rlast         : out std_logic;                                         -- rlast
            s0_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s0_axi4_rvalid        : out std_logic;                                         -- rvalid
            s0_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s0_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s0_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s0_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s0_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s0_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s0_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s0_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s0_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s0_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s0_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s0_axi4_awready       : out std_logic;                                         -- awready
            s0_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s0_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s0_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s0_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s0_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s0_axi4_wready        : out std_logic;                                         -- wready
            s0_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s0_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s0_axi4_bvalid        : out std_logic;                                         -- bvalid
            s0_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s1_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s1_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s1_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s1_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s1_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s1_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s1_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s1_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s1_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s1_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s1_axi4_arready       : out std_logic;                                         -- arready
            s1_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s1_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s1_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s1_axi4_rlast         : out std_logic;                                         -- rlast
            s1_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s1_axi4_rvalid        : out std_logic;                                         -- rvalid
            s1_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s1_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s1_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s1_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s1_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s1_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s1_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s1_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s1_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s1_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s1_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s1_axi4_awready       : out std_logic;                                         -- awready
            s1_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s1_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s1_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s1_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s1_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s1_axi4_wready        : out std_logic;                                         -- wready
            s1_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s1_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s1_axi4_bvalid        : out std_logic;                                         -- bvalid
            s1_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s2_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s2_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s2_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s2_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s2_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s2_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s2_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s2_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s2_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s2_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s2_axi4_arready       : out std_logic;                                         -- arready
            s2_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s2_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s2_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s2_axi4_rlast         : out std_logic;                                         -- rlast
            s2_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s2_axi4_rvalid        : out std_logic;                                         -- rvalid
            s2_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s2_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s2_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s2_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s2_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s2_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s2_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s2_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s2_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s2_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s2_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s2_axi4_awready       : out std_logic;                                         -- awready
            s2_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s2_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s2_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s2_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s2_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s2_axi4_wready        : out std_logic;                                         -- wready
            s2_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s2_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s2_axi4_bvalid        : out std_logic;                                         -- bvalid
            s2_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s3_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s3_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s3_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s3_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s3_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s3_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s3_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s3_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s3_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s3_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s3_axi4_arready       : out std_logic;                                         -- arready
            s3_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s3_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s3_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s3_axi4_rlast         : out std_logic;                                         -- rlast
            s3_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s3_axi4_rvalid        : out std_logic;                                         -- rvalid
            s3_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s3_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s3_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s3_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s3_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s3_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s3_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s3_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s3_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s3_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s3_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s3_axi4_awready       : out std_logic;                                         -- awready
            s3_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s3_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s3_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s3_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s3_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s3_axi4_wready        : out std_logic;                                         -- wready
            s3_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s3_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s3_axi4_bvalid        : out std_logic;                                         -- bvalid
            s3_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s4_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s4_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s4_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s4_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s4_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s4_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s4_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s4_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s4_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s4_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s4_axi4_arready       : out std_logic;                                         -- arready
            s4_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s4_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s4_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s4_axi4_rlast         : out std_logic;                                         -- rlast
            s4_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s4_axi4_rvalid        : out std_logic;                                         -- rvalid
            s4_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s4_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s4_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s4_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s4_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s4_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s4_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s4_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s4_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s4_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s4_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s4_axi4_awready       : out std_logic;                                         -- awready
            s4_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s4_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s4_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s4_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s4_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s4_axi4_wready        : out std_logic;                                         -- wready
            s4_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s4_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s4_axi4_bvalid        : out std_logic;                                         -- bvalid
            s4_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s5_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s5_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s5_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s5_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s5_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s5_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s5_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s5_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s5_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s5_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s5_axi4_arready       : out std_logic;                                         -- arready
            s5_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s5_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s5_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s5_axi4_rlast         : out std_logic;                                         -- rlast
            s5_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s5_axi4_rvalid        : out std_logic;                                         -- rvalid
            s5_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s5_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s5_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s5_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s5_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s5_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s5_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s5_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s5_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s5_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s5_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s5_axi4_awready       : out std_logic;                                         -- awready
            s5_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s5_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s5_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s5_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s5_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s5_axi4_wready        : out std_logic;                                         -- wready
            s5_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s5_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s5_axi4_bvalid        : out std_logic;                                         -- bvalid
            s5_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s6_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s6_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s6_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s6_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s6_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s6_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s6_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s6_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s6_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s6_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s6_axi4_arready       : out std_logic;                                         -- arready
            s6_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s6_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s6_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s6_axi4_rlast         : out std_logic;                                         -- rlast
            s6_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s6_axi4_rvalid        : out std_logic;                                         -- rvalid
            s6_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s6_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s6_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s6_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s6_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s6_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s6_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s6_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s6_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s6_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s6_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s6_axi4_awready       : out std_logic;                                         -- awready
            s6_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s6_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s6_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s6_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s6_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s6_axi4_wready        : out std_logic;                                         -- wready
            s6_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s6_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s6_axi4_bvalid        : out std_logic;                                         -- bvalid
            s6_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s7_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s7_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s7_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s7_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s7_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s7_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s7_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s7_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s7_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s7_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s7_axi4_arready       : out std_logic;                                         -- arready
            s7_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s7_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s7_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s7_axi4_rlast         : out std_logic;                                         -- rlast
            s7_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s7_axi4_rvalid        : out std_logic;                                         -- rvalid
            s7_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s7_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s7_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s7_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s7_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s7_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s7_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s7_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s7_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s7_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s7_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s7_axi4_awready       : out std_logic;                                         -- awready
            s7_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s7_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s7_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s7_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s7_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s7_axi4_wready        : out std_logic;                                         -- wready
            s7_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s7_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s7_axi4_bvalid        : out std_logic;                                         -- bvalid
            s7_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s8_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s8_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s8_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s8_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s8_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s8_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s8_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s8_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s8_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s8_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s8_axi4_arready       : out std_logic;                                         -- arready
            s8_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s8_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s8_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s8_axi4_rlast         : out std_logic;                                         -- rlast
            s8_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s8_axi4_rvalid        : out std_logic;                                         -- rvalid
            s8_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s8_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s8_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s8_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s8_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s8_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s8_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s8_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s8_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s8_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s8_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s8_axi4_awready       : out std_logic;                                         -- awready
            s8_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s8_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s8_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s8_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s8_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s8_axi4_wready        : out std_logic;                                         -- wready
            s8_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s8_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s8_axi4_bvalid        : out std_logic;                                         -- bvalid
            s8_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s9_axi4_arid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s9_axi4_araddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s9_axi4_arlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s9_axi4_arsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s9_axi4_arburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s9_axi4_arlock        : in  std_logic                      := 'X';             -- arlock
            s9_axi4_arprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s9_axi4_arqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s9_axi4_aruser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s9_axi4_arvalid       : in  std_logic                      := 'X';             -- arvalid
            s9_axi4_arready       : out std_logic;                                         -- arready
            s9_axi4_rid           : out std_logic_vector(6 downto 0);                      -- rid
            s9_axi4_rdata         : out std_logic_vector(255 downto 0);                    -- rdata
            s9_axi4_rresp         : out std_logic_vector(1 downto 0);                      -- rresp
            s9_axi4_rlast         : out std_logic;                                         -- rlast
            s9_axi4_ruser         : out std_logic_vector(31 downto 0);                     -- ruser
            s9_axi4_rvalid        : out std_logic;                                         -- rvalid
            s9_axi4_rready        : in  std_logic                      := 'X';             -- rready
            s9_axi4_awid          : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s9_axi4_awaddr        : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s9_axi4_awlen         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s9_axi4_awsize        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s9_axi4_awburst       : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s9_axi4_awlock        : in  std_logic                      := 'X';             -- awlock
            s9_axi4_awprot        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s9_axi4_awqos         : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s9_axi4_awuser        : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s9_axi4_awvalid       : in  std_logic                      := 'X';             -- awvalid
            s9_axi4_awready       : out std_logic;                                         -- awready
            s9_axi4_wdata         : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s9_axi4_wstrb         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s9_axi4_wlast         : in  std_logic                      := 'X';             -- wlast
            s9_axi4_wuser         : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s9_axi4_wvalid        : in  std_logic                      := 'X';             -- wvalid
            s9_axi4_wready        : out std_logic;                                         -- wready
            s9_axi4_bid           : out std_logic_vector(6 downto 0);                      -- bid
            s9_axi4_bresp         : out std_logic_vector(1 downto 0);                      -- bresp
            s9_axi4_bvalid        : out std_logic;                                         -- bvalid
            s9_axi4_bready        : in  std_logic                      := 'X';             -- bready
            s10_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s10_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s10_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s10_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s10_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s10_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s10_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s10_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s10_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s10_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s10_axi4_arready      : out std_logic;                                         -- arready
            s10_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s10_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s10_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s10_axi4_rlast        : out std_logic;                                         -- rlast
            s10_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s10_axi4_rvalid       : out std_logic;                                         -- rvalid
            s10_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s10_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s10_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s10_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s10_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s10_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s10_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s10_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s10_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s10_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s10_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s10_axi4_awready      : out std_logic;                                         -- awready
            s10_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s10_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s10_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s10_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s10_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s10_axi4_wready       : out std_logic;                                         -- wready
            s10_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s10_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s10_axi4_bvalid       : out std_logic;                                         -- bvalid
            s10_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s11_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s11_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s11_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s11_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s11_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s11_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s11_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s11_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s11_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s11_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s11_axi4_arready      : out std_logic;                                         -- arready
            s11_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s11_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s11_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s11_axi4_rlast        : out std_logic;                                         -- rlast
            s11_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s11_axi4_rvalid       : out std_logic;                                         -- rvalid
            s11_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s11_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s11_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s11_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s11_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s11_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s11_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s11_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s11_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s11_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s11_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s11_axi4_awready      : out std_logic;                                         -- awready
            s11_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s11_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s11_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s11_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s11_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s11_axi4_wready       : out std_logic;                                         -- wready
            s11_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s11_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s11_axi4_bvalid       : out std_logic;                                         -- bvalid
            s11_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s12_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s12_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s12_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s12_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s12_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s12_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s12_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s12_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s12_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s12_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s12_axi4_arready      : out std_logic;                                         -- arready
            s12_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s12_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s12_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s12_axi4_rlast        : out std_logic;                                         -- rlast
            s12_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s12_axi4_rvalid       : out std_logic;                                         -- rvalid
            s12_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s12_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s12_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s12_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s12_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s12_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s12_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s12_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s12_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s12_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s12_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s12_axi4_awready      : out std_logic;                                         -- awready
            s12_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s12_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s12_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s12_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s12_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s12_axi4_wready       : out std_logic;                                         -- wready
            s12_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s12_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s12_axi4_bvalid       : out std_logic;                                         -- bvalid
            s12_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s13_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s13_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s13_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s13_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s13_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s13_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s13_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s13_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s13_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s13_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s13_axi4_arready      : out std_logic;                                         -- arready
            s13_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s13_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s13_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s13_axi4_rlast        : out std_logic;                                         -- rlast
            s13_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s13_axi4_rvalid       : out std_logic;                                         -- rvalid
            s13_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s13_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s13_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s13_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s13_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s13_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s13_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s13_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s13_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s13_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s13_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s13_axi4_awready      : out std_logic;                                         -- awready
            s13_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s13_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s13_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s13_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s13_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s13_axi4_wready       : out std_logic;                                         -- wready
            s13_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s13_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s13_axi4_bvalid       : out std_logic;                                         -- bvalid
            s13_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s14_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s14_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s14_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s14_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s14_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s14_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s14_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s14_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s14_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s14_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s14_axi4_arready      : out std_logic;                                         -- arready
            s14_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s14_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s14_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s14_axi4_rlast        : out std_logic;                                         -- rlast
            s14_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s14_axi4_rvalid       : out std_logic;                                         -- rvalid
            s14_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s14_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s14_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s14_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s14_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s14_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s14_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s14_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s14_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s14_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s14_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s14_axi4_awready      : out std_logic;                                         -- awready
            s14_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s14_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s14_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s14_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s14_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s14_axi4_wready       : out std_logic;                                         -- wready
            s14_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s14_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s14_axi4_bvalid       : out std_logic;                                         -- bvalid
            s14_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s15_axi4_arid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- arid
            s15_axi4_araddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- araddr
            s15_axi4_arlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            s15_axi4_arsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            s15_axi4_arburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            s15_axi4_arlock       : in  std_logic                      := 'X';             -- arlock
            s15_axi4_arprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            s15_axi4_arqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            s15_axi4_aruser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- aruser
            s15_axi4_arvalid      : in  std_logic                      := 'X';             -- arvalid
            s15_axi4_arready      : out std_logic;                                         -- arready
            s15_axi4_rid          : out std_logic_vector(6 downto 0);                      -- rid
            s15_axi4_rdata        : out std_logic_vector(255 downto 0);                    -- rdata
            s15_axi4_rresp        : out std_logic_vector(1 downto 0);                      -- rresp
            s15_axi4_rlast        : out std_logic;                                         -- rlast
            s15_axi4_ruser        : out std_logic_vector(31 downto 0);                     -- ruser
            s15_axi4_rvalid       : out std_logic;                                         -- rvalid
            s15_axi4_rready       : in  std_logic                      := 'X';             -- rready
            s15_axi4_awid         : in  std_logic_vector(6 downto 0)   := (others => 'X'); -- awid
            s15_axi4_awaddr       : in  std_logic_vector(43 downto 0)  := (others => 'X'); -- awaddr
            s15_axi4_awlen        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            s15_axi4_awsize       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            s15_axi4_awburst      : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            s15_axi4_awlock       : in  std_logic                      := 'X';             -- awlock
            s15_axi4_awprot       : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            s15_axi4_awqos        : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            s15_axi4_awuser       : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- awuser
            s15_axi4_awvalid      : in  std_logic                      := 'X';             -- awvalid
            s15_axi4_awready      : out std_logic;                                         -- awready
            s15_axi4_wdata        : in  std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            s15_axi4_wstrb        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            s15_axi4_wlast        : in  std_logic                      := 'X';             -- wlast
            s15_axi4_wuser        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser
            s15_axi4_wvalid       : in  std_logic                      := 'X';             -- wvalid
            s15_axi4_wready       : out std_logic;                                         -- wready
            s15_axi4_bid          : out std_logic_vector(6 downto 0);                      -- bid
            s15_axi4_bresp        : out std_logic_vector(1 downto 0);                      -- bresp
            s15_axi4_bvalid       : out std_logic;                                         -- bvalid
            s15_axi4_bready       : in  std_logic                      := 'X';             -- bready
            s0_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s0_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s1_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s1_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s2_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s2_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s3_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s3_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s4_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s4_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s5_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s5_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s6_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s6_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s7_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s7_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s8_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s8_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s9_axi4_aclk          : in  std_logic                      := 'X';             -- clk
            s9_axi4_aresetn       : in  std_logic                      := 'X';             -- reset_n
            s10_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s10_axi4_aresetn      : in  std_logic                      := 'X';             -- reset_n
            s11_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s11_axi4_aresetn      : in  std_logic                      := 'X';             -- reset_n
            s12_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s12_axi4_aresetn      : in  std_logic                      := 'X';             -- reset_n
            s13_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s13_axi4_aresetn      : in  std_logic                      := 'X';             -- reset_n
            s14_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s14_axi4_aresetn      : in  std_logic                      := 'X';             -- reset_n
            s15_axi4_aclk         : in  std_logic                      := 'X';             -- clk
            s15_axi4_aresetn      : in  std_logic                      := 'X'              -- reset_n
        );
    end component noc_initiator;

begin

    noc_init_c : component noc_initiator
    port map (
        s0_axi4_aclk          => NOC_AXI_CLK(0),
        s1_axi4_aclk          => NOC_AXI_CLK(1),
        s2_axi4_aclk          => NOC_AXI_CLK(2),
        s3_axi4_aclk          => NOC_AXI_CLK(3),
        s4_axi4_aclk          => NOC_AXI_CLK(4),
        s5_axi4_aclk          => NOC_AXI_CLK(5),
        s6_axi4_aclk          => NOC_AXI_CLK(6),
        s7_axi4_aclk          => NOC_AXI_CLK(7),
        s8_axi4_aclk          => NOC_AXI_CLK(8),
        s9_axi4_aclk          => NOC_AXI_CLK(9),
        s10_axi4_aclk         => NOC_AXI_CLK(10),
        s11_axi4_aclk         => NOC_AXI_CLK(11),
        s12_axi4_aclk         => NOC_AXI_CLK(12),
        s13_axi4_aclk         => NOC_AXI_CLK(13),
        s14_axi4_aclk         => NOC_AXI_CLK(14),
        s15_axi4_aclk         => NOC_AXI_CLK(15),

        s0_axi4_aresetn       => NOC_AXI_RST_N(0),
        s1_axi4_aresetn       => NOC_AXI_RST_N(1),
        s2_axi4_aresetn       => NOC_AXI_RST_N(2),
        s3_axi4_aresetn       => NOC_AXI_RST_N(3),
        s4_axi4_aresetn       => NOC_AXI_RST_N(4),
        s5_axi4_aresetn       => NOC_AXI_RST_N(5),
        s6_axi4_aresetn       => NOC_AXI_RST_N(6),
        s7_axi4_aresetn       => NOC_AXI_RST_N(7),
        s8_axi4_aresetn       => NOC_AXI_RST_N(8),
        s9_axi4_aresetn       => NOC_AXI_RST_N(9),
        s10_axi4_aresetn      => NOC_AXI_RST_N(10),
        s11_axi4_aresetn      => NOC_AXI_RST_N(11),
        s12_axi4_aresetn      => NOC_AXI_RST_N(12),
        s13_axi4_aresetn      => NOC_AXI_RST_N(13),
        s14_axi4_aresetn      => NOC_AXI_RST_N(14),
        s15_axi4_aresetn      => NOC_AXI_RST_N(15),

        -- Master 0 AXI interface
        s0_axi4_awid          => NOC_AXI_AWID(0),
        s0_axi4_awaddr        => NOC_AXI_AWADDR(0),
        s0_axi4_awlen         => NOC_AXI_AWLEN(0),
        s0_axi4_awsize        => NOC_AXI_AWSIZE(0),
        s0_axi4_awburst       => NOC_AXI_AWBURST(0),
        s0_axi4_awprot        => "010",
        s0_axi4_awqos         => "1111",
        s0_axi4_awuser        => (0 => '1', others => '0'),
        s0_axi4_awvalid       => NOC_AXI_AWVALID(0),
        s0_axi4_awready       => NOC_AXI_AWREADY(0),

        s0_axi4_wdata         => NOC_AXI_WDATA(0),
        s0_axi4_wstrb         => NOC_AXI_WSTRB(0),
        s0_axi4_wlast         => NOC_AXI_WLAST(0),
        s0_axi4_wvalid        => NOC_AXI_WVALID(0),
        s0_axi4_wready        => NOC_AXI_WREADY(0),

        s0_axi4_bid           => NOC_AXI_BID(0),
        s0_axi4_bresp         => NOC_AXI_BRESP(0),
        s0_axi4_bvalid        => NOC_AXI_BVALID(0),
        s0_axi4_bready        => NOC_AXI_BREADY(0),

        s0_axi4_arid          => NOC_AXI_ARID(0),
        s0_axi4_araddr        => NOC_AXI_ARADDR(0),
        s0_axi4_arlen         => NOC_AXI_ARLEN(0),
        s0_axi4_arsize        => NOC_AXI_ARSIZE(0),
        s0_axi4_arburst       => NOC_AXI_ARBURST(0),
        s0_axi4_arprot        => "010",
        s0_axi4_arqos         => "1111",
        s0_axi4_aruser        => (0 => '1', others => '0'),
        s0_axi4_arvalid       => NOC_AXI_ARVALID(0),
        s0_axi4_arready       => NOC_AXI_ARREADY(0),

        s0_axi4_rid           => NOC_AXI_RID(0),
        s0_axi4_rdata         => NOC_AXI_RDATA(0),
        s0_axi4_rresp         => NOC_AXI_RRESP(0),
        s0_axi4_rlast         => NOC_AXI_RLAST(0),
        s0_axi4_rvalid        => NOC_AXI_RVALID(0),
        s0_axi4_rready        => NOC_AXI_RREADY(0),

        -- Master 1 AXI interface
        s1_axi4_awid          => NOC_AXI_AWID(1),
        s1_axi4_awaddr        => NOC_AXI_AWADDR(1),
        s1_axi4_awlen         => NOC_AXI_AWLEN(1),
        s1_axi4_awsize        => NOC_AXI_AWSIZE(1),
        s1_axi4_awburst       => NOC_AXI_AWBURST(1),
        s1_axi4_awprot        => "010",
        s1_axi4_awqos         => "1111",
        s1_axi4_awuser        => (0 => '1', others => '0'),
        s1_axi4_awvalid       => NOC_AXI_AWVALID(1),
        s1_axi4_awready       => NOC_AXI_AWREADY(1),

        s1_axi4_wdata         => NOC_AXI_WDATA(1),
        s1_axi4_wstrb         => NOC_AXI_WSTRB(1),
        s1_axi4_wlast         => NOC_AXI_WLAST(1),
        s1_axi4_wvalid        => NOC_AXI_WVALID(1),
        s1_axi4_wready        => NOC_AXI_WREADY(1),

        s1_axi4_bid           => NOC_AXI_BID(1),
        s1_axi4_bresp         => NOC_AXI_BRESP(1),
        s1_axi4_bvalid        => NOC_AXI_BVALID(1),
        s1_axi4_bready        => NOC_AXI_BREADY(1),

        s1_axi4_arid          => NOC_AXI_ARID(1),
        s1_axi4_araddr        => NOC_AXI_ARADDR(1),
        s1_axi4_arlen         => NOC_AXI_ARLEN(1),
        s1_axi4_arsize        => NOC_AXI_ARSIZE(1),
        s1_axi4_arburst       => NOC_AXI_ARBURST(1),
        s1_axi4_arprot        => "010",
        s1_axi4_arqos         => "1111",
        s1_axi4_aruser        => (0 => '1', others => '0'),
        s1_axi4_arvalid       => NOC_AXI_ARVALID(1),
        s1_axi4_arready       => NOC_AXI_ARREADY(1),

        s1_axi4_rid           => NOC_AXI_RID(1),
        s1_axi4_rdata         => NOC_AXI_RDATA(1),
        s1_axi4_rresp         => NOC_AXI_RRESP(1),
        s1_axi4_rlast         => NOC_AXI_RLAST(1),
        s1_axi4_rvalid        => NOC_AXI_RVALID(1),
        s1_axi4_rready        => NOC_AXI_RREADY(1),

        -- Master 2 AXI interface
        s2_axi4_awid          => NOC_AXI_AWID(2),
        s2_axi4_awaddr        => NOC_AXI_AWADDR(2),
        s2_axi4_awlen         => NOC_AXI_AWLEN(2),
        s2_axi4_awsize        => NOC_AXI_AWSIZE(2),
        s2_axi4_awburst       => NOC_AXI_AWBURST(2),
        s2_axi4_awprot        => "010",
        s2_axi4_awqos         => "1111",
        s2_axi4_awuser        => (0 => '1', others => '0'),
        s2_axi4_awvalid       => NOC_AXI_AWVALID(2),
        s2_axi4_awready       => NOC_AXI_AWREADY(2),

        s2_axi4_wdata         => NOC_AXI_WDATA(2),
        s2_axi4_wstrb         => NOC_AXI_WSTRB(2),
        s2_axi4_wlast         => NOC_AXI_WLAST(2),
        s2_axi4_wvalid        => NOC_AXI_WVALID(2),
        s2_axi4_wready        => NOC_AXI_WREADY(2),

        s2_axi4_bid           => NOC_AXI_BID(2),
        s2_axi4_bresp         => NOC_AXI_BRESP(2),
        s2_axi4_bvalid        => NOC_AXI_BVALID(2),
        s2_axi4_bready        => NOC_AXI_BREADY(2),

        s2_axi4_arid          => NOC_AXI_ARID(2),
        s2_axi4_araddr        => NOC_AXI_ARADDR(2),
        s2_axi4_arlen         => NOC_AXI_ARLEN(2),
        s2_axi4_arsize        => NOC_AXI_ARSIZE(2),
        s2_axi4_arburst       => NOC_AXI_ARBURST(2),
        s2_axi4_arprot        => "010",
        s2_axi4_arqos         => "1111",
        s2_axi4_aruser        => (0 => '1', others => '0'),
        s2_axi4_arvalid       => NOC_AXI_ARVALID(2),
        s2_axi4_arready       => NOC_AXI_ARREADY(2),

        s2_axi4_rid           => NOC_AXI_RID(2),
        s2_axi4_rdata         => NOC_AXI_RDATA(2),
        s2_axi4_rresp         => NOC_AXI_RRESP(2),
        s2_axi4_rlast         => NOC_AXI_RLAST(2),
        s2_axi4_rvalid        => NOC_AXI_RVALID(2),
        s2_axi4_rready        => NOC_AXI_RREADY(2),

        -- Master 3 AXI interface
        s3_axi4_awid          => NOC_AXI_AWID(3),
        s3_axi4_awaddr        => NOC_AXI_AWADDR(3),
        s3_axi4_awlen         => NOC_AXI_AWLEN(3),
        s3_axi4_awsize        => NOC_AXI_AWSIZE(3),
        s3_axi4_awburst       => NOC_AXI_AWBURST(3),
        s3_axi4_awprot        => "010",
        s3_axi4_awqos         => "1111",
        s3_axi4_awuser        => (0 => '1', others => '0'),
        s3_axi4_awvalid       => NOC_AXI_AWVALID(3),
        s3_axi4_awready       => NOC_AXI_AWREADY(3),

        s3_axi4_wdata         => NOC_AXI_WDATA(3),
        s3_axi4_wstrb         => NOC_AXI_WSTRB(3),
        s3_axi4_wlast         => NOC_AXI_WLAST(3),
        s3_axi4_wvalid        => NOC_AXI_WVALID(3),
        s3_axi4_wready        => NOC_AXI_WREADY(3),

        s3_axi4_bid           => NOC_AXI_BID(3),
        s3_axi4_bresp         => NOC_AXI_BRESP(3),
        s3_axi4_bvalid        => NOC_AXI_BVALID(3),
        s3_axi4_bready        => NOC_AXI_BREADY(3),

        s3_axi4_arid          => NOC_AXI_ARID(3),
        s3_axi4_araddr        => NOC_AXI_ARADDR(3),
        s3_axi4_arlen         => NOC_AXI_ARLEN(3),
        s3_axi4_arsize        => NOC_AXI_ARSIZE(3),
        s3_axi4_arburst       => NOC_AXI_ARBURST(3),
        s3_axi4_arprot        => "010",
        s3_axi4_arqos         => "1111",
        s3_axi4_aruser        => (0 => '1', others => '0'),
        s3_axi4_arvalid       => NOC_AXI_ARVALID(3),
        s3_axi4_arready       => NOC_AXI_ARREADY(3),

        s3_axi4_rid           => NOC_AXI_RID(3),
        s3_axi4_rdata         => NOC_AXI_RDATA(3),
        s3_axi4_rresp         => NOC_AXI_RRESP(3),
        s3_axi4_rlast         => NOC_AXI_RLAST(3),
        s3_axi4_rvalid        => NOC_AXI_RVALID(3),
        s3_axi4_rready        => NOC_AXI_RREADY(3),

        -- Master 4 AXI interface
        s4_axi4_awid          => NOC_AXI_AWID(4),
        s4_axi4_awaddr        => NOC_AXI_AWADDR(4),
        s4_axi4_awlen         => NOC_AXI_AWLEN(4),
        s4_axi4_awsize        => NOC_AXI_AWSIZE(4),
        s4_axi4_awburst       => NOC_AXI_AWBURST(4),
        s4_axi4_awprot        => "010",
        s4_axi4_awqos         => "1111",
        s4_axi4_awuser        => (0 => '1', others => '0'),
        s4_axi4_awvalid       => NOC_AXI_AWVALID(4),
        s4_axi4_awready       => NOC_AXI_AWREADY(4),

        s4_axi4_wdata         => NOC_AXI_WDATA(4),
        s4_axi4_wstrb         => NOC_AXI_WSTRB(4),
        s4_axi4_wlast         => NOC_AXI_WLAST(4),
        s4_axi4_wvalid        => NOC_AXI_WVALID(4),
        s4_axi4_wready        => NOC_AXI_WREADY(4),

        s4_axi4_bid           => NOC_AXI_BID(4),
        s4_axi4_bresp         => NOC_AXI_BRESP(4),
        s4_axi4_bvalid        => NOC_AXI_BVALID(4),
        s4_axi4_bready        => NOC_AXI_BREADY(4),

        s4_axi4_arid          => NOC_AXI_ARID(4),
        s4_axi4_araddr        => NOC_AXI_ARADDR(4),
        s4_axi4_arlen         => NOC_AXI_ARLEN(4),
        s4_axi4_arsize        => NOC_AXI_ARSIZE(4),
        s4_axi4_arburst       => NOC_AXI_ARBURST(4),
        s4_axi4_arprot        => "010",
        s4_axi4_arqos         => "1111",
        s4_axi4_aruser        => (0 => '1', others => '0'),
        s4_axi4_arvalid       => NOC_AXI_ARVALID(4),
        s4_axi4_arready       => NOC_AXI_ARREADY(4),

        s4_axi4_rid           => NOC_AXI_RID(4),
        s4_axi4_rdata         => NOC_AXI_RDATA(4),
        s4_axi4_rresp         => NOC_AXI_RRESP(4),
        s4_axi4_rlast         => NOC_AXI_RLAST(4),
        s4_axi4_rvalid        => NOC_AXI_RVALID(4),
        s4_axi4_rready        => NOC_AXI_RREADY(4),

        -- Master 5 AXI interface
        s5_axi4_awid          => NOC_AXI_AWID(5),
        s5_axi4_awaddr        => NOC_AXI_AWADDR(5),
        s5_axi4_awlen         => NOC_AXI_AWLEN(5),
        s5_axi4_awsize        => NOC_AXI_AWSIZE(5),
        s5_axi4_awburst       => NOC_AXI_AWBURST(5),
        s5_axi4_awprot        => "010",
        s5_axi4_awqos         => "1111",
        s5_axi4_awuser        => (0 => '1', others => '0'),
        s5_axi4_awvalid       => NOC_AXI_AWVALID(5),
        s5_axi4_awready       => NOC_AXI_AWREADY(5),

        s5_axi4_wdata         => NOC_AXI_WDATA(5),
        s5_axi4_wstrb         => NOC_AXI_WSTRB(5),
        s5_axi4_wlast         => NOC_AXI_WLAST(5),
        s5_axi4_wvalid        => NOC_AXI_WVALID(5),
        s5_axi4_wready        => NOC_AXI_WREADY(5),

        s5_axi4_bid           => NOC_AXI_BID(5),
        s5_axi4_bresp         => NOC_AXI_BRESP(5),
        s5_axi4_bvalid        => NOC_AXI_BVALID(5),
        s5_axi4_bready        => NOC_AXI_BREADY(5),

        s5_axi4_arid          => NOC_AXI_ARID(5),
        s5_axi4_araddr        => NOC_AXI_ARADDR(5),
        s5_axi4_arlen         => NOC_AXI_ARLEN(5),
        s5_axi4_arsize        => NOC_AXI_ARSIZE(5),
        s5_axi4_arburst       => NOC_AXI_ARBURST(5),
        s5_axi4_arprot        => "010",
        s5_axi4_arqos         => "1111",
        s5_axi4_aruser        => (0 => '1', others => '0'),
        s5_axi4_arvalid       => NOC_AXI_ARVALID(5),
        s5_axi4_arready       => NOC_AXI_ARREADY(5),

        s5_axi4_rid           => NOC_AXI_RID(5),
        s5_axi4_rdata         => NOC_AXI_RDATA(5),
        s5_axi4_rresp         => NOC_AXI_RRESP(5),
        s5_axi4_rlast         => NOC_AXI_RLAST(5),
        s5_axi4_rvalid        => NOC_AXI_RVALID(5),
        s5_axi4_rready        => NOC_AXI_RREADY(5),

        -- Master 6 AXI interface
        s6_axi4_awid          => NOC_AXI_AWID(6),
        s6_axi4_awaddr        => NOC_AXI_AWADDR(6),
        s6_axi4_awlen         => NOC_AXI_AWLEN(6),
        s6_axi4_awsize        => NOC_AXI_AWSIZE(6),
        s6_axi4_awburst       => NOC_AXI_AWBURST(6),
        s6_axi4_awprot        => "010",
        s6_axi4_awqos         => "1111",
        s6_axi4_awuser        => (0 => '1', others => '0'),
        s6_axi4_awvalid       => NOC_AXI_AWVALID(6),
        s6_axi4_awready       => NOC_AXI_AWREADY(6),

        s6_axi4_wdata         => NOC_AXI_WDATA(6),
        s6_axi4_wstrb         => NOC_AXI_WSTRB(6),
        s6_axi4_wlast         => NOC_AXI_WLAST(6),
        s6_axi4_wvalid        => NOC_AXI_WVALID(6),
        s6_axi4_wready        => NOC_AXI_WREADY(6),

        s6_axi4_bid           => NOC_AXI_BID(6),
        s6_axi4_bresp         => NOC_AXI_BRESP(6),
        s6_axi4_bvalid        => NOC_AXI_BVALID(6),
        s6_axi4_bready        => NOC_AXI_BREADY(6),

        s6_axi4_arid          => NOC_AXI_ARID(6),
        s6_axi4_araddr        => NOC_AXI_ARADDR(6),
        s6_axi4_arlen         => NOC_AXI_ARLEN(6),
        s6_axi4_arsize        => NOC_AXI_ARSIZE(6),
        s6_axi4_arburst       => NOC_AXI_ARBURST(6),
        s6_axi4_arprot        => "010",
        s6_axi4_arqos         => "1111",
        s6_axi4_aruser        => (0 => '1', others => '0'),
        s6_axi4_arvalid       => NOC_AXI_ARVALID(6),
        s6_axi4_arready       => NOC_AXI_ARREADY(6),

        s6_axi4_rid           => NOC_AXI_RID(6),
        s6_axi4_rdata         => NOC_AXI_RDATA(6),
        s6_axi4_rresp         => NOC_AXI_RRESP(6),
        s6_axi4_rlast         => NOC_AXI_RLAST(6),
        s6_axi4_rvalid        => NOC_AXI_RVALID(6),
        s6_axi4_rready        => NOC_AXI_RREADY(6),

        -- Master 7 AXI interface
        s7_axi4_awid          => NOC_AXI_AWID(7),
        s7_axi4_awaddr        => NOC_AXI_AWADDR(7),
        s7_axi4_awlen         => NOC_AXI_AWLEN(7),
        s7_axi4_awsize        => NOC_AXI_AWSIZE(7),
        s7_axi4_awburst       => NOC_AXI_AWBURST(7),
        s7_axi4_awprot        => "010",
        s7_axi4_awqos         => "1111",
        s7_axi4_awuser        => (0 => '1', others => '0'),
        s7_axi4_awvalid       => NOC_AXI_AWVALID(7),
        s7_axi4_awready       => NOC_AXI_AWREADY(7),

        s7_axi4_wdata         => NOC_AXI_WDATA(7),
        s7_axi4_wstrb         => NOC_AXI_WSTRB(7),
        s7_axi4_wlast         => NOC_AXI_WLAST(7),
        s7_axi4_wvalid        => NOC_AXI_WVALID(7),
        s7_axi4_wready        => NOC_AXI_WREADY(7),

        s7_axi4_bid           => NOC_AXI_BID(7),
        s7_axi4_bresp         => NOC_AXI_BRESP(7),
        s7_axi4_bvalid        => NOC_AXI_BVALID(7),
        s7_axi4_bready        => NOC_AXI_BREADY(7),

        s7_axi4_arid          => NOC_AXI_ARID(7),
        s7_axi4_araddr        => NOC_AXI_ARADDR(7),
        s7_axi4_arlen         => NOC_AXI_ARLEN(7),
        s7_axi4_arsize        => NOC_AXI_ARSIZE(7),
        s7_axi4_arburst       => NOC_AXI_ARBURST(7),
        s7_axi4_arprot        => "010",
        s7_axi4_arqos         => "1111",
        s7_axi4_aruser        => (0 => '1', others => '0'),
        s7_axi4_arvalid       => NOC_AXI_ARVALID(7),
        s7_axi4_arready       => NOC_AXI_ARREADY(7),

        s7_axi4_rid           => NOC_AXI_RID(7),
        s7_axi4_rdata         => NOC_AXI_RDATA(7),
        s7_axi4_rresp         => NOC_AXI_RRESP(7),
        s7_axi4_rlast         => NOC_AXI_RLAST(7),
        s7_axi4_rvalid        => NOC_AXI_RVALID(7),
        s7_axi4_rready        => NOC_AXI_RREADY(7),

        -- Master 8 AXI interface
        s8_axi4_awid          => NOC_AXI_AWID(8),
        s8_axi4_awaddr        => NOC_AXI_AWADDR(8),
        s8_axi4_awlen         => NOC_AXI_AWLEN(8),
        s8_axi4_awsize        => NOC_AXI_AWSIZE(8),
        s8_axi4_awburst       => NOC_AXI_AWBURST(8),
        s8_axi4_awprot        => "010",
        s8_axi4_awqos         => "1111",
        s8_axi4_awuser        => (0 => '1', others => '0'),
        s8_axi4_awvalid       => NOC_AXI_AWVALID(8),
        s8_axi4_awready       => NOC_AXI_AWREADY(8),

        s8_axi4_wdata         => NOC_AXI_WDATA(8),
        s8_axi4_wstrb         => NOC_AXI_WSTRB(8),
        s8_axi4_wlast         => NOC_AXI_WLAST(8),
        s8_axi4_wvalid        => NOC_AXI_WVALID(8),
        s8_axi4_wready        => NOC_AXI_WREADY(8),

        s8_axi4_bid           => NOC_AXI_BID(8),
        s8_axi4_bresp         => NOC_AXI_BRESP(8),
        s8_axi4_bvalid        => NOC_AXI_BVALID(8),
        s8_axi4_bready        => NOC_AXI_BREADY(8),

        s8_axi4_arid          => NOC_AXI_ARID(8),
        s8_axi4_araddr        => NOC_AXI_ARADDR(8),
        s8_axi4_arlen         => NOC_AXI_ARLEN(8),
        s8_axi4_arsize        => NOC_AXI_ARSIZE(8),
        s8_axi4_arburst       => NOC_AXI_ARBURST(8),
        s8_axi4_arprot        => "010",
        s8_axi4_arqos         => "1111",
        s8_axi4_aruser        => (0 => '1', others => '0'),
        s8_axi4_arvalid       => NOC_AXI_ARVALID(8),
        s8_axi4_arready       => NOC_AXI_ARREADY(8),

        s8_axi4_rid           => NOC_AXI_RID(8),
        s8_axi4_rdata         => NOC_AXI_RDATA(8),
        s8_axi4_rresp         => NOC_AXI_RRESP(8),
        s8_axi4_rlast         => NOC_AXI_RLAST(8),
        s8_axi4_rvalid        => NOC_AXI_RVALID(8),
        s8_axi4_rready        => NOC_AXI_RREADY(8),

        -- Master 9 AXI interface
        s9_axi4_awid          => NOC_AXI_AWID(9),
        s9_axi4_awaddr        => NOC_AXI_AWADDR(9),
        s9_axi4_awlen         => NOC_AXI_AWLEN(9),
        s9_axi4_awsize        => NOC_AXI_AWSIZE(9),
        s9_axi4_awburst       => NOC_AXI_AWBURST(9),
        s9_axi4_awprot        => "010",
        s9_axi4_awqos         => "1111",
        s9_axi4_awuser        => (0 => '1', others => '0'),
        s9_axi4_awvalid       => NOC_AXI_AWVALID(9),
        s9_axi4_awready       => NOC_AXI_AWREADY(9),

        s9_axi4_wdata         => NOC_AXI_WDATA(9),
        s9_axi4_wstrb         => NOC_AXI_WSTRB(9),
        s9_axi4_wlast         => NOC_AXI_WLAST(9),
        s9_axi4_wvalid        => NOC_AXI_WVALID(9),
        s9_axi4_wready        => NOC_AXI_WREADY(9),

        s9_axi4_bid           => NOC_AXI_BID(9),
        s9_axi4_bresp         => NOC_AXI_BRESP(9),
        s9_axi4_bvalid        => NOC_AXI_BVALID(9),
        s9_axi4_bready        => NOC_AXI_BREADY(9),

        s9_axi4_arid          => NOC_AXI_ARID(9),
        s9_axi4_araddr        => NOC_AXI_ARADDR(9),
        s9_axi4_arlen         => NOC_AXI_ARLEN(9),
        s9_axi4_arsize        => NOC_AXI_ARSIZE(9),
        s9_axi4_arburst       => NOC_AXI_ARBURST(9),
        s9_axi4_arprot        => "010",
        s9_axi4_arqos         => "1111",
        s9_axi4_aruser        => (0 => '1', others => '0'),
        s9_axi4_arvalid       => NOC_AXI_ARVALID(9),
        s9_axi4_arready       => NOC_AXI_ARREADY(9),

        s9_axi4_rid           => NOC_AXI_RID(9),
        s9_axi4_rdata         => NOC_AXI_RDATA(9),
        s9_axi4_rresp         => NOC_AXI_RRESP(9),
        s9_axi4_rlast         => NOC_AXI_RLAST(9),
        s9_axi4_rvalid        => NOC_AXI_RVALID(9),
        s9_axi4_rready        => NOC_AXI_RREADY(9),

        -- Master 10 AXI interface
        s10_axi4_awid         => NOC_AXI_AWID(10),
        s10_axi4_awaddr       => NOC_AXI_AWADDR(10),
        s10_axi4_awlen        => NOC_AXI_AWLEN(10),
        s10_axi4_awsize       => NOC_AXI_AWSIZE(10),
        s10_axi4_awburst      => NOC_AXI_AWBURST(10),
        s10_axi4_awprot       => "010",
        s10_axi4_awqos        => "1111",
        s10_axi4_awuser       => (0 => '1', others => '0'),
        s10_axi4_awvalid      => NOC_AXI_AWVALID(10),
        s10_axi4_awready      => NOC_AXI_AWREADY(10),

        s10_axi4_wdata        => NOC_AXI_WDATA(10),
        s10_axi4_wstrb        => NOC_AXI_WSTRB(10),
        s10_axi4_wlast        => NOC_AXI_WLAST(10),
        s10_axi4_wvalid       => NOC_AXI_WVALID(10),
        s10_axi4_wready       => NOC_AXI_WREADY(10),

        s10_axi4_bid          => NOC_AXI_BID(10),
        s10_axi4_bresp        => NOC_AXI_BRESP(10),
        s10_axi4_bvalid       => NOC_AXI_BVALID(10),
        s10_axi4_bready       => NOC_AXI_BREADY(10),

        s10_axi4_arid         => NOC_AXI_ARID(10),
        s10_axi4_araddr       => NOC_AXI_ARADDR(10),
        s10_axi4_arlen        => NOC_AXI_ARLEN(10),
        s10_axi4_arsize       => NOC_AXI_ARSIZE(10),
        s10_axi4_arburst      => NOC_AXI_ARBURST(10),
        s10_axi4_arprot       => "010",
        s10_axi4_arqos        => "1111",
        s10_axi4_aruser       => (0 => '1', others => '0'),
        s10_axi4_arvalid      => NOC_AXI_ARVALID(10),
        s10_axi4_arready      => NOC_AXI_ARREADY(10),

        s10_axi4_rid          => NOC_AXI_RID(10),
        s10_axi4_rdata        => NOC_AXI_RDATA(10),
        s10_axi4_rresp        => NOC_AXI_RRESP(10),
        s10_axi4_rlast        => NOC_AXI_RLAST(10),
        s10_axi4_rvalid       => NOC_AXI_RVALID(10),
        s10_axi4_rready       => NOC_AXI_RREADY(10),

        -- Master 11 AXI interface
        s11_axi4_awid         => NOC_AXI_AWID(11),
        s11_axi4_awaddr       => NOC_AXI_AWADDR(11),
        s11_axi4_awlen        => NOC_AXI_AWLEN(11),
        s11_axi4_awsize       => NOC_AXI_AWSIZE(11),
        s11_axi4_awburst      => NOC_AXI_AWBURST(11),
        s11_axi4_awprot       => "010",
        s11_axi4_awqos        => "1111",
        s11_axi4_awuser       => (0 => '1', others => '0'),
        s11_axi4_awvalid      => NOC_AXI_AWVALID(11),
        s11_axi4_awready      => NOC_AXI_AWREADY(11),

        s11_axi4_wdata        => NOC_AXI_WDATA(11),
        s11_axi4_wstrb        => NOC_AXI_WSTRB(11),
        s11_axi4_wlast        => NOC_AXI_WLAST(11),
        s11_axi4_wvalid       => NOC_AXI_WVALID(11),
        s11_axi4_wready       => NOC_AXI_WREADY(11),

        s11_axi4_bid          => NOC_AXI_BID(11),
        s11_axi4_bresp        => NOC_AXI_BRESP(11),
        s11_axi4_bvalid       => NOC_AXI_BVALID(11),
        s11_axi4_bready       => NOC_AXI_BREADY(11),

        s11_axi4_arid         => NOC_AXI_ARID(11),
        s11_axi4_araddr       => NOC_AXI_ARADDR(11),
        s11_axi4_arlen        => NOC_AXI_ARLEN(11),
        s11_axi4_arsize       => NOC_AXI_ARSIZE(11),
        s11_axi4_arburst      => NOC_AXI_ARBURST(11),
        s11_axi4_arprot       => "010",
        s11_axi4_arqos        => "1111",
        s11_axi4_aruser       => (0 => '1', others => '0'),
        s11_axi4_arvalid      => NOC_AXI_ARVALID(11),
        s11_axi4_arready      => NOC_AXI_ARREADY(11),

        s11_axi4_rid          => NOC_AXI_RID(11),
        s11_axi4_rdata        => NOC_AXI_RDATA(11),
        s11_axi4_rresp        => NOC_AXI_RRESP(11),
        s11_axi4_rlast        => NOC_AXI_RLAST(11),
        s11_axi4_rvalid       => NOC_AXI_RVALID(11),
        s11_axi4_rready       => NOC_AXI_RREADY(11),

        -- Master 12 AXI interface
        s12_axi4_awid         => NOC_AXI_AWID(12),
        s12_axi4_awaddr       => NOC_AXI_AWADDR(12),
        s12_axi4_awlen        => NOC_AXI_AWLEN(12),
        s12_axi4_awsize       => NOC_AXI_AWSIZE(12),
        s12_axi4_awburst      => NOC_AXI_AWBURST(12),
        s12_axi4_awprot       => "010",
        s12_axi4_awqos        => "1111",
        s12_axi4_awuser       => (0 => '1', others => '0'),
        s12_axi4_awvalid      => NOC_AXI_AWVALID(12),
        s12_axi4_awready      => NOC_AXI_AWREADY(12),

        s12_axi4_wdata        => NOC_AXI_WDATA(12),
        s12_axi4_wstrb        => NOC_AXI_WSTRB(12),
        s12_axi4_wlast        => NOC_AXI_WLAST(12),
        s12_axi4_wvalid       => NOC_AXI_WVALID(12),
        s12_axi4_wready       => NOC_AXI_WREADY(12),

        s12_axi4_bid          => NOC_AXI_BID(12),
        s12_axi4_bresp        => NOC_AXI_BRESP(12),
        s12_axi4_bvalid       => NOC_AXI_BVALID(12),
        s12_axi4_bready       => NOC_AXI_BREADY(12),

        s12_axi4_arid         => NOC_AXI_ARID(12),
        s12_axi4_araddr       => NOC_AXI_ARADDR(12),
        s12_axi4_arlen        => NOC_AXI_ARLEN(12),
        s12_axi4_arsize       => NOC_AXI_ARSIZE(12),
        s12_axi4_arburst      => NOC_AXI_ARBURST(12),
        s12_axi4_arprot       => "010",
        s12_axi4_arqos        => "1111",
        s12_axi4_aruser       => (0 => '1', others => '0'),
        s12_axi4_arvalid      => NOC_AXI_ARVALID(12),
        s12_axi4_arready      => NOC_AXI_ARREADY(12),

        s12_axi4_rid          => NOC_AXI_RID(12),
        s12_axi4_rdata        => NOC_AXI_RDATA(12),
        s12_axi4_rresp        => NOC_AXI_RRESP(12),
        s12_axi4_rlast        => NOC_AXI_RLAST(12),
        s12_axi4_rvalid       => NOC_AXI_RVALID(12),
        s12_axi4_rready       => NOC_AXI_RREADY(12),

        -- Master 13 AXI interface
        s13_axi4_awid         => NOC_AXI_AWID(13),
        s13_axi4_awaddr       => NOC_AXI_AWADDR(13),
        s13_axi4_awlen        => NOC_AXI_AWLEN(13),
        s13_axi4_awsize       => NOC_AXI_AWSIZE(13),
        s13_axi4_awburst      => NOC_AXI_AWBURST(13),
        s13_axi4_awprot       => "010",
        s13_axi4_awqos        => "1111",
        s13_axi4_awuser       => (0 => '1', others => '0'),
        s13_axi4_awvalid      => NOC_AXI_AWVALID(13),
        s13_axi4_awready      => NOC_AXI_AWREADY(13),

        s13_axi4_wdata        => NOC_AXI_WDATA(13),
        s13_axi4_wstrb        => NOC_AXI_WSTRB(13),
        s13_axi4_wlast        => NOC_AXI_WLAST(13),
        s13_axi4_wvalid       => NOC_AXI_WVALID(13),
        s13_axi4_wready       => NOC_AXI_WREADY(13),

        s13_axi4_bid          => NOC_AXI_BID(13),
        s13_axi4_bresp        => NOC_AXI_BRESP(13),
        s13_axi4_bvalid       => NOC_AXI_BVALID(13),
        s13_axi4_bready       => NOC_AXI_BREADY(13),

        s13_axi4_arid         => NOC_AXI_ARID(13),
        s13_axi4_araddr       => NOC_AXI_ARADDR(13),
        s13_axi4_arlen        => NOC_AXI_ARLEN(13),
        s13_axi4_arsize       => NOC_AXI_ARSIZE(13),
        s13_axi4_arburst      => NOC_AXI_ARBURST(13),
        s13_axi4_arprot       => "010",
        s13_axi4_arqos        => "1111",
        s13_axi4_aruser       => (0 => '1', others => '0'),
        s13_axi4_arvalid      => NOC_AXI_ARVALID(13),
        s13_axi4_arready      => NOC_AXI_ARREADY(13),

        s13_axi4_rid          => NOC_AXI_RID(13),
        s13_axi4_rdata        => NOC_AXI_RDATA(13),
        s13_axi4_rresp        => NOC_AXI_RRESP(13),
        s13_axi4_rlast        => NOC_AXI_RLAST(13),
        s13_axi4_rvalid       => NOC_AXI_RVALID(13),
        s13_axi4_rready       => NOC_AXI_RREADY(13),

        -- Master 14 AXI interface
        s14_axi4_awid          => NOC_AXI_AWID(14),
        s14_axi4_awaddr        => NOC_AXI_AWADDR(14),
        s14_axi4_awlen         => NOC_AXI_AWLEN(14),
        s14_axi4_awsize        => NOC_AXI_AWSIZE(14),
        s14_axi4_awburst       => NOC_AXI_AWBURST(14),
        s14_axi4_awprot        => "010",
        s14_axi4_awqos         => "1111",
        s14_axi4_awuser        => (0 => '1', others => '0'),
        s14_axi4_awvalid       => NOC_AXI_AWVALID(14),
        s14_axi4_awready       => NOC_AXI_AWREADY(14),

        s14_axi4_wdata         => NOC_AXI_WDATA(14),
        s14_axi4_wstrb         => NOC_AXI_WSTRB(14),
        s14_axi4_wlast         => NOC_AXI_WLAST(14),
        s14_axi4_wvalid        => NOC_AXI_WVALID(14),
        s14_axi4_wready        => NOC_AXI_WREADY(14),

        s14_axi4_bid           => NOC_AXI_BID(14),
        s14_axi4_bresp         => NOC_AXI_BRESP(14),
        s14_axi4_bvalid        => NOC_AXI_BVALID(14),
        s14_axi4_bready        => NOC_AXI_BREADY(14),

        s14_axi4_arid          => NOC_AXI_ARID(14),
        s14_axi4_araddr        => NOC_AXI_ARADDR(14),
        s14_axi4_arlen         => NOC_AXI_ARLEN(14),
        s14_axi4_arsize        => NOC_AXI_ARSIZE(14),
        s14_axi4_arburst       => NOC_AXI_ARBURST(14),
        s14_axi4_arprot        => "010",
        s14_axi4_arqos         => "1111",
        s14_axi4_aruser        => (0 => '1', others => '0'),
        s14_axi4_arvalid       => NOC_AXI_ARVALID(14),
        s14_axi4_arready       => NOC_AXI_ARREADY(14),

        s14_axi4_rid           => NOC_AXI_RID(14),
        s14_axi4_rdata         => NOC_AXI_RDATA(14),
        s14_axi4_rresp         => NOC_AXI_RRESP(14),
        s14_axi4_rlast         => NOC_AXI_RLAST(14),
        s14_axi4_rvalid        => NOC_AXI_RVALID(14),
        s14_axi4_rready        => NOC_AXI_RREADY(14),

        -- Master 15 AXI interface
        s15_axi4_awid          => NOC_AXI_AWID(15),
        s15_axi4_awaddr        => NOC_AXI_AWADDR(15),
        s15_axi4_awlen         => NOC_AXI_AWLEN(15),
        s15_axi4_awsize        => NOC_AXI_AWSIZE(15),
        s15_axi4_awburst       => NOC_AXI_AWBURST(15),
        s15_axi4_awprot        => "010",
        s15_axi4_awqos         => "1111",
        s15_axi4_awuser        => (0 => '1', others => '0'),
        s15_axi4_awvalid       => NOC_AXI_AWVALID(15),
        s15_axi4_awready       => NOC_AXI_AWREADY(15),

        s15_axi4_wdata         => NOC_AXI_WDATA(15),
        s15_axi4_wstrb         => NOC_AXI_WSTRB(15),
        s15_axi4_wlast         => NOC_AXI_WLAST(15),
        s15_axi4_wvalid        => NOC_AXI_WVALID(15),
        s15_axi4_wready        => NOC_AXI_WREADY(15),

        s15_axi4_bid           => NOC_AXI_BID(15),
        s15_axi4_bresp         => NOC_AXI_BRESP(15),
        s15_axi4_bvalid        => NOC_AXI_BVALID(15),
        s15_axi4_bready        => NOC_AXI_BREADY(15),

        s15_axi4_arid          => NOC_AXI_ARID(15),
        s15_axi4_araddr        => NOC_AXI_ARADDR(15),
        s15_axi4_arlen         => NOC_AXI_ARLEN(15),
        s15_axi4_arsize        => NOC_AXI_ARSIZE(15),
        s15_axi4_arburst       => NOC_AXI_ARBURST(15),
        s15_axi4_arprot        => "010",
        s15_axi4_arqos         => "1111",
        s15_axi4_aruser        => (0 => '1', others => '0'),
        s15_axi4_arvalid       => NOC_AXI_ARVALID(15),
        s15_axi4_arready       => NOC_AXI_ARREADY(15),

        s15_axi4_rid           => NOC_AXI_RID(15),
        s15_axi4_rdata         => NOC_AXI_RDATA(15),
        s15_axi4_rresp         => NOC_AXI_RRESP(15),
        s15_axi4_rlast         => NOC_AXI_RLAST(15),
        s15_axi4_rvalid        => NOC_AXI_RVALID(15),
        s15_axi4_rready        => NOC_AXI_RREADY(15)
    );

end architecture;
