-- noc_init_ent.vhd: NoC initiator entity
-- Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.type_pack.all;

entity NOC_INIT is
generic (
    -- Currently only 16 is possible
    NOC_PORTS           : natural := 16;
    NOC_AXI_ID_WIDTH    : natural := 7;
    NOC_AXI_ADDR_WIDTH  : natural := 44;
    NOC_AXI_LEN_WIDTH   : natural := 8;
    NOC_AXI_SIZE_WIDTH  : natural := 3;
    NOC_AXI_BURST_WIDTH : natural := 2;
    NOC_AXI_DATA_WIDTH  : natural := 512;
    NOC_AXI_RESP_WIDTH  : natural := 2
);
port (
    NOC_BRIDGE_CLK  : in std_logic;

    NOC_AXI_CLK     : in std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_RST_N   : in std_logic_vector(NOC_PORTS-1 downto 0);

    NOC_AXI_AWID    : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ID_WIDTH-1 downto 0);
    NOC_AXI_AWADDR  : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ADDR_WIDTH-1 downto 0);
    NOC_AXI_AWLEN   : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_LEN_WIDTH-1 downto 0);
    NOC_AXI_AWSIZE  : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_SIZE_WIDTH-1 downto 0);
    NOC_AXI_AWBURST : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_BURST_WIDTH-1 downto 0);
    NOC_AXI_AWVALID : in  std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_AWREADY : out std_logic_vector(NOC_PORTS-1 downto 0);

    NOC_AXI_WDATA   : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_DATA_WIDTH-1 downto 0);
    NOC_AXI_WSTRB   : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_DATA_WIDTH/8-1 downto 0);
    NOC_AXI_WLAST   : in  std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_WVALID  : in  std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_WREADY  : out std_logic_vector(NOC_PORTS-1 downto 0);

    NOC_AXI_BID     : out slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ID_WIDTH-1 downto 0);
    NOC_AXI_BRESP   : out slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_RESP_WIDTH-1 downto 0);
    NOC_AXI_BVALID  : out std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_BREADY  : in  std_logic_vector(NOC_PORTS-1 downto 0);

    NOC_AXI_ARID    : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ID_WIDTH-1 downto 0);
    NOC_AXI_ARADDR  : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ADDR_WIDTH-1 downto 0);
    NOC_AXI_ARLEN   : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_LEN_WIDTH-1 downto 0);
    NOC_AXI_ARSIZE  : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_SIZE_WIDTH-1 downto 0);
    NOC_AXI_ARBURST : in  slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_BURST_WIDTH-1 downto 0);
    NOC_AXI_ARVALID : in  std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_ARREADY : out std_logic_vector(NOC_PORTS-1 downto 0);

    NOC_AXI_RID     : out slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_ID_WIDTH-1 downto 0);
    NOC_AXI_RDATA   : out slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_DATA_WIDTH-1 downto 0);
    NOC_AXI_RRESP   : out slv_array_t(NOC_PORTS-1 downto 0)(NOC_AXI_RESP_WIDTH-1 downto 0);
    NOC_AXI_RLAST   : out std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_RVALID  : out std_logic_vector(NOC_PORTS-1 downto 0);
    NOC_AXI_RREADY  : in  std_logic_vector(NOC_PORTS-1 downto 0)
);
end entity;
