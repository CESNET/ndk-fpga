-- versal_axi_switch.vhd : Switch between two AXI masters. This not universal
--                         axi switch component, communication state is not
--                         tracked. Therefore, the two masters must synchronise
--                         themselfs outside of this component to avoid
--                         simultanous comunication of the two masters.
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

entity VERSAL_AXI_SWITCH is
    generic (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH : natural := 32;
        -- Address word width in bits 32 or 64
        -- Use 64 if accessing via NOC, 32 otherwise
        AXI_ADDR_WIDTH : natural := 32;
        -- Target device
        DEVICE         : string  := "VERSAL"
    );
    port (
        -- =====================================================================
        -- Select signal
        -- =====================================================================
        SEL            : in  std_logic;

        -- =====================================================================
        -- AXI4 interface (slaves)
        -- =====================================================================
        AXI_S0_AWID    : in  std_logic_vector(8-1 downto 0);
        AXI_S0_AWADDR  : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_S0_AWLEN   : in  std_logic_vector(8-1 downto 0);
        AXI_S0_AWSIZE  : in  std_logic_vector(3-1 downto 0);
        AXI_S0_AWBURST : in  std_logic_vector(2-1 downto 0);
        AXI_S0_AWPROT  : in  std_logic_vector(3-1 downto 0);
        AXI_S0_AWVALID : in  std_logic;
        AXI_S0_AWREADY : out std_logic;
        AXI_S0_WDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_S0_WSTRB   : in  std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_S0_WLAST   : in  std_logic;
        AXI_S0_WVALID  : in  std_logic;
        AXI_S0_WREADY  : out std_logic;
        AXI_S0_BID     : out std_logic_vector(8-1 downto 0);
        AXI_S0_BRESP   : out std_logic_vector(2-1 downto 0);
        AXI_S0_BVALID  : out std_logic;
        AXI_S0_BREADY  : in  std_logic;
        AXI_S0_ARID    : in  std_logic_vector(8-1 downto 0);
        AXI_S0_ARADDR  : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_S0_ARLEN   : in  std_logic_vector(8-1 downto 0);
        AXI_S0_ARSIZE  : in  std_logic_vector(3-1 downto 0);
        AXI_S0_ARBURST : in  std_logic_vector(2-1 downto 0);
        AXI_S0_ARPROT  : in  std_logic_vector(3-1 downto 0);
        AXI_S0_ARVALID : in  std_logic;
        AXI_S0_ARREADY : out std_logic;
        AXI_S0_RID     : out std_logic_vector(8-1 downto 0);
        AXI_S0_RDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_S0_RRESP   : out std_logic_vector(2-1 downto 0);
        AXI_S0_RLAST   : out std_logic;
        AXI_S0_RVALID  : out std_logic;
        AXI_S0_RREADY  : in  std_logic;

        AXI_S1_AWID    : in  std_logic_vector(8-1 downto 0);
        AXI_S1_AWADDR  : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_S1_AWLEN   : in  std_logic_vector(8-1 downto 0);
        AXI_S1_AWSIZE  : in  std_logic_vector(3-1 downto 0);
        AXI_S1_AWBURST : in  std_logic_vector(2-1 downto 0);
        AXI_S1_AWPROT  : in  std_logic_vector(3-1 downto 0);
        AXI_S1_AWVALID : in  std_logic;
        AXI_S1_AWREADY : out std_logic;
        AXI_S1_WDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_S1_WSTRB   : in  std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_S1_WLAST   : in  std_logic;
        AXI_S1_WVALID  : in  std_logic;
        AXI_S1_WREADY  : out std_logic;
        AXI_S1_BID     : out std_logic_vector(8-1 downto 0);
        AXI_S1_BRESP   : out std_logic_vector(2-1 downto 0);
        AXI_S1_BVALID  : out std_logic;
        AXI_S1_BREADY  : in  std_logic;
        AXI_S1_ARID    : in  std_logic_vector(8-1 downto 0);
        AXI_S1_ARADDR  : in  std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_S1_ARLEN   : in  std_logic_vector(8-1 downto 0);
        AXI_S1_ARSIZE  : in  std_logic_vector(3-1 downto 0);
        AXI_S1_ARBURST : in  std_logic_vector(2-1 downto 0);
        AXI_S1_ARPROT  : in  std_logic_vector(3-1 downto 0);
        AXI_S1_ARVALID : in  std_logic;
        AXI_S1_ARREADY : out std_logic;
        AXI_S1_RID     : out std_logic_vector(8-1 downto 0);
        AXI_S1_RDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_S1_RRESP   : out std_logic_vector(2-1 downto 0);
        AXI_S1_RLAST   : out std_logic;
        AXI_S1_RVALID  : out std_logic;
        AXI_S1_RREADY  : in  std_logic;

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID       : out std_logic_vector(8-1 downto 0);
        AXI_AWADDR     : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWLEN      : out std_logic_vector(8-1 downto 0);
        AXI_AWSIZE     : out std_logic_vector(3-1 downto 0);
        AXI_AWBURST    : out std_logic_vector(2-1 downto 0);
        AXI_AWPROT     : out std_logic_vector(3-1 downto 0);
        AXI_AWVALID    : out std_logic;
        AXI_AWREADY    : in  std_logic;
        AXI_WDATA      : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB      : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_WLAST      : out std_logic;
        AXI_WVALID     : out std_logic;
        AXI_WREADY     : in  std_logic;
        AXI_BID        : in  std_logic_vector(8-1 downto 0);
        AXI_BRESP      : in  std_logic_vector(2-1 downto 0);
        AXI_BVALID     : in  std_logic;
        AXI_BREADY     : out std_logic;
        AXI_ARID       : out std_logic_vector(8-1 downto 0);
        AXI_ARADDR     : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_ARLEN      : out std_logic_vector(8-1 downto 0);
        AXI_ARSIZE     : out std_logic_vector(3-1 downto 0);
        AXI_ARBURST    : out std_logic_vector(2-1 downto 0);
        AXI_ARPROT     : out std_logic_vector(3-1 downto 0);
        AXI_ARVALID    : out std_logic;
        AXI_ARREADY    : in  std_logic;
        AXI_RID        : in  std_logic_vector(8-1 downto 0);
        AXI_RDATA      : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_RRESP      : in  std_logic_vector(2-1 downto 0);
        AXI_RLAST      : in  std_logic;
        AXI_RVALID     : in  std_logic;
        AXI_RREADY     : out std_logic
    );

end entity;

architecture FULL of VERSAL_AXI_SWITCH is
begin
    AXI_AWID    <= AXI_S1_AWID    when SEL = '1' else AXI_S0_AWID;
    AXI_AWADDR  <= AXI_S1_AWADDR  when SEL = '1' else AXI_S0_AWADDR;
    AXI_AWLEN   <= AXI_S1_AWLEN   when SEL = '1' else AXI_S0_AWLEN;
    AXI_AWSIZE  <= AXI_S1_AWSIZE  when SEL = '1' else AXI_S0_AWSIZE;
    AXI_AWBURST <= AXI_S1_AWBURST when SEL = '1' else AXI_S0_AWBURST;
    AXI_AWPROT  <= AXI_S1_AWPROT  when SEL = '1' else AXI_S0_AWPROT;
    AXI_AWVALID <= AXI_S1_AWVALID when SEL = '1' else AXI_S0_AWVALID;
    AXI_WDATA   <= AXI_S1_WDATA   when SEL = '1' else AXI_S0_WDATA;
    AXI_WSTRB   <= AXI_S1_WSTRB   when SEL = '1' else AXI_S0_WSTRB;
    AXI_WLAST   <= AXI_S1_WLAST   when SEL = '1' else AXI_S0_WLAST;
    AXI_WVALID  <= AXI_S1_WVALID  when SEL = '1' else AXI_S0_WVALID;
    AXI_BREADY  <= AXI_S1_BREADY  when SEL = '1' else AXI_S0_BREADY;
    AXI_ARID    <= AXI_S1_ARID    when SEL = '1' else AXI_S0_ARID;
    AXI_ARADDR  <= AXI_S1_ARADDR  when SEL = '1' else AXI_S0_ARADDR;
    AXI_ARLEN   <= AXI_S1_ARLEN   when SEL = '1' else AXI_S0_ARLEN;
    AXI_ARSIZE  <= AXI_S1_ARSIZE  when SEL = '1' else AXI_S0_ARSIZE;
    AXI_ARBURST <= AXI_S1_ARBURST when SEL = '1' else AXI_S0_ARBURST;
    AXI_ARPROT  <= AXI_S1_ARPROT  when SEL = '1' else AXI_S0_ARPROT;
    AXI_ARVALID <= AXI_S1_ARVALID when SEL = '1' else AXI_S0_ARVALID;
    AXI_RREADY  <= AXI_S1_RREADY  when SEL = '1' else AXI_S0_RREADY;

    AXI_S0_AWREADY <= AXI_AWREADY when SEL = '0' else '0';
    AXI_S0_WREADY  <= AXI_WREADY  when SEL = '0' else '0';
    AXI_S0_BID     <= AXI_BID     when SEL = '0' else (others => '0');
    AXI_S0_BRESP   <= AXI_BRESP   when SEL = '0' else (others => '0');
    AXI_S0_BVALID  <= AXI_BVALID  when SEL = '0' else '0';
    AXI_S0_ARREADY <= AXI_ARREADY when SEL = '0' else '0';
    AXI_S0_RID     <= AXI_RID     when SEL = '0' else (others => '0');
    AXI_S0_RDATA   <= AXI_RDATA   when SEL = '0' else (others => '0');
    AXI_S0_RRESP   <= AXI_RRESP   when SEL = '0' else (others => '0');
    AXI_S0_RLAST   <= AXI_RLAST   when SEL = '0' else '0';
    AXI_S0_RVALID  <= AXI_RVALID  when SEL = '0' else '0';

    AXI_S1_AWREADY <= AXI_AWREADY when SEL = '1' else '0';
    AXI_S1_WREADY  <= AXI_WREADY  when SEL = '1' else '0';
    AXI_S1_BID     <= AXI_BID     when SEL = '1' else (others => '0');
    AXI_S1_BRESP   <= AXI_BRESP   when SEL = '1' else (others => '0');
    AXI_S1_BVALID  <= AXI_BVALID  when SEL = '1' else '0';
    AXI_S1_ARREADY <= AXI_ARREADY when SEL = '1' else '0';
    AXI_S1_RID     <= AXI_RID     when SEL = '1' else (others => '0');
    AXI_S1_RDATA   <= AXI_RDATA   when SEL = '1' else (others => '0');
    AXI_S1_RRESP   <= AXI_RRESP   when SEL = '1' else (others => '0');
    AXI_S1_RLAST   <= AXI_RLAST   when SEL = '1' else '0';
    AXI_S1_RVALID  <= AXI_RVALID  when SEL = '1' else '0';
end architecture;
