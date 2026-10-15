-- testbench.vhd: Testbench for VERSAL_FPGA_ID component
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is
    constant CLKPER         : time := 10 ns;           -- Clock period
    constant RESET_TIME     : time := 2*CLKPER + 1 ns; -- Reset duration

    --! Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;

    --! VERSAL_FPGA_ID parameters
    constant AXI_DATA_WIDTH : natural := 32;
    constant AXI_ADDR_WIDTH : natural := 32;

    --! input and output
    -- FPGA ID from NDK
    signal fpga_id          : std_logic_vector(127 downto 0);
    signal fpga_id_vld      : std_logic;

    -- AXI4 signals
    signal axi_awid    : std_logic_vector(8-1 downto 0);
    signal axi_awaddr  : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal axi_awlen   : std_logic_vector(8-1 downto 0);
    signal axi_awsize  : std_logic_vector(3-1 downto 0);
    signal axi_awburst : std_logic_vector(2-1 downto 0);
    signal axi_awprot  : std_logic_vector(3-1 downto 0);
    signal axi_awvalid : std_logic;
    signal axi_awready : std_logic;
    signal axi_wdata   : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_wstrb   : std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
    signal axi_wlast   : std_logic;
    signal axi_wvalid  : std_logic;
    signal axi_wready  : std_logic;
    signal axi_bid     : std_logic_vector(8-1 downto 0);
    signal axi_bresp   : std_logic_vector(2-1 downto 0);
    signal axi_bvalid  : std_logic;
    signal axi_bready  : std_logic;
    signal axi_arid    : std_logic_vector(8-1 downto 0);
    signal axi_araddr  : std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
    signal axi_arlen   : std_logic_vector(8-1 downto 0);
    signal axi_arsize  : std_logic_vector(3-1 downto 0);
    signal axi_arburst : std_logic_vector(2-1 downto 0);
    signal axi_arprot  : std_logic_vector(3-1 downto 0);
    signal axi_arvalid : std_logic;
    signal axi_arready : std_logic;
    signal axi_rid     : std_logic_vector(8-1 downto 0);
    signal axi_rdata   : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_rresp   : std_logic_vector(2-1 downto 0);
    signal axi_rlast   : std_logic;
    signal axi_rvalid  : std_logic;
    signal axi_rready  : std_logic;
begin

    --! VERSAL_FPGA_ID
    uut : entity work.VERSAL_FPGA_ID
    generic map (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH => 32,
        -- Address word width in bits 32 or 64
        AXI_ADDR_WIDTH => 32,
        -- Target device
        DEVICE         => "VERSAL"
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => clk,
        RESET       => reset,

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    => axi_awid,
        AXI_AWADDR  => axi_awaddr,
        AXI_AWLEN   => axi_awlen,
        AXI_AWSIZE  => axi_awsize,
        AXI_AWBURST => axi_awburst,
        AXI_AWPROT  => axi_awprot,
        AXI_AWVALID => axi_awvalid,
        AXI_AWREADY => axi_awready,
        AXI_WDATA   => axi_wdata,
        AXI_WSTRB   => axi_wstrb,
        AXI_WLAST   => axi_wlast,
        AXI_WVALID  => axi_wvalid,
        AXI_WREADY  => axi_wready,
        AXI_BID     => axi_bid,
        AXI_BRESP   => axi_bresp,
        AXI_BVALID  => axi_bvalid,
        AXI_BREADY  => axi_bready,
        AXI_ARID    => axi_arid,
        AXI_ARADDR  => axi_araddr,
        AXI_ARLEN   => axi_arlen,
        AXI_ARSIZE  => axi_arsize,
        AXI_ARBURST => axi_arburst,
        AXI_ARPROT  => axi_arprot,
        AXI_ARVALID => axi_arvalid,
        AXI_ARREADY => axi_arready,
        AXI_RID     => axi_rid,
        AXI_RDATA   => axi_rdata,
        AXI_RRESP   => axi_rresp,
        AXI_RLAST   => axi_rlast,
        AXI_RVALID  => axi_rvalid,
        AXI_RREADY  => axi_rready,

        -- =====================================================================
        -- FPGA_ID interface
        -- =====================================================================
        FPGA_ID     => fpga_id,
        FPGA_ID_VLD => fpga_id_vld
    );

    -- Generate clock
    clk_gen_p : process
    begin
        clk <= '1';
        wait for CLKPER/2;
        clk <= '0';
        wait for CLKPER/2;
    end process;

    -- Generate reset
    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    --! Simulating input flow
    input_flow : process
        variable data : std_logic_vector(31 downto 0);
        variable addr : std_logic_vector(31 downto 0);
        variable be   : std_logic_vector(3 downto 0);
    begin
        be          := "1111";
        --! Initialize input interface
        axi_awready <= '1';
        axi_wready  <= '1';
        axi_bid     <= (others => '0');
        axi_bresp   <= (others => '0');
        axi_bvalid  <= '0';
        axi_arready <= '1';
        axi_rid     <= (others => '0');
        axi_rdata   <= (others => '0');
        axi_rresp   <= (others => '0');
        axi_rlast   <= '0';
        axi_rvalid  <= '0';

        wait for RESET_TIME;

        wait until axi_arvalid = '1';

        axi_rdata  <= X"11111111";
        axi_rlast  <= '1';
        axi_rvalid <= '1';
        wait for CLKPER;
        wait until axi_arvalid = '1';
        axi_rdata  <= X"22222222";
        axi_rlast  <= '1';
        axi_rvalid <= '1';
        wait for CLKPER;
        wait until axi_arvalid = '1';
        axi_rdata  <= X"33333333";
        axi_rlast  <= '1';
        axi_rvalid <= '1';
        wait for CLKPER;
        wait until axi_arvalid = '1';
        axi_rdata  <= X"44444444";
        axi_rlast  <= '1';
        axi_rvalid <= '1';
        wait for CLKPER;

        wait;

    end process;
end architecture;
