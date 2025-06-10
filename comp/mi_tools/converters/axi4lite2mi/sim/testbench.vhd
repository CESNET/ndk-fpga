-- testbench.vhd: Testbench for AXI4LITE2MI component
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2025
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

    -- AXI4LITE2MI generics
    -- Data word width in bits, must be 32
    constant DATA_WIDTH  : natural := 32;
    -- Address word width in bits
    constant ADDR_WIDTH  : natural := 32;
    -- Address mask vector
    constant ADDR_MASK   : std_logic_vector(ADDR_WIDTH-1 downto 0) := (others => '1');

    --! Clock and reset signals
    signal clk              : std_logic;
    signal reset            : std_logic;


    -- MI signals
    signal mi_dwr     : std_logic_vector(31 downto 0);
    signal mi_addr    : std_logic_vector(31 downto 0);
    signal mi_be      : std_logic_vector(3 downto 0);
    signal mi_drd     : std_logic_vector(31 downto 0);
    signal mi_rd      : std_logic;
    signal mi_wr      : std_logic;
    signal mi_ardy    : std_logic;
    signal mi_drdy    : std_logic;

    -- AXI4-Lite
    signal axi_awaddr      : std_logic_vector(ADDR_WIDTH - 1 downto 0);
    signal axi_awvalid     : std_logic;
    signal axi_awready     : std_logic;

    signal axi_wdata       : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal axi_wstrb       : std_logic_vector(DATA_WIDTH / 8 - 1 downto 0);
    signal axi_wvalid      : std_logic;
    signal axi_wready      : std_logic;

    signal axi_bresp       : std_logic_vector(1 downto 0);
    signal axi_bvalid      : std_logic;
    signal axi_bready      : std_logic;

    signal axi_araddr      : std_logic_vector(ADDR_WIDTH - 1 downto 0);
    signal axi_arvalid     : std_logic;
    signal axi_arready     : std_logic;

    signal axi_rdata       : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal axi_rresp       : std_logic_vector(1 downto 0);
    signal axi_rvalid      : std_logic;
    signal axi_rready      : std_logic;
begin

    --! AXI4LITE2MI
    uut : entity work.AXI4LITE2MI
    generic map (
        DATA_WIDTH => DATA_WIDTH,
        ADDR_WIDTH => ADDR_WIDTH,
        ADDR_MASK  => ADDR_MASK
    )
    port map (
        -- Clock and reset
        CLK         => clk,
        RESET       => reset,

        -- AXI4 Lite
        AXI_AWADDR  => axi_awaddr,
        AXI_AWVALID => axi_awvalid,
        AXI_AWREADY => axi_awready,

        AXI_WDATA   => axi_wdata,
        AXI_WSTRB   => axi_wstrb,
        AXI_WVALID  => axi_wvalid,
        AXI_WREADY  => axi_wready,

        AXI_BRESP   => axi_bresp,
        AXI_BVALID  => axi_bvalid,
        AXI_BREADY  => axi_bready,

        AXI_ARADDR  => axi_araddr,
        AXI_ARVALID => axi_arvalid,
        AXI_ARREADY => axi_arready,

        AXI_RDATA   => axi_rdata,
        AXI_RRESP   => axi_rresp,
        AXI_RVALID  => axi_rvalid,
        AXI_RREADY  => axi_rready,

        -- MI interface
        MI_DWR      => mi_dwr,
        MI_ADDR     => mi_addr,
        MI_BE       => mi_be,
        MI_RD       => mi_rd,
        MI_WR       => mi_wr,
        MI_ARDY     => mi_ardy,
        MI_DRD      => mi_drd,
        MI_DRDY     => mi_drdy
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
    --
    -- MI_ARDY <= MI_RD or MI_WR;
    -- MI_DRDY <= MI_RD;

    --! Simulating input flow
    input_flow : process
    begin
        axi_awaddr  <= (others => '0');
        axi_awvalid <= '0';

        axi_wdata  <= (others => '0');
        axi_wstrb  <= (others => '1');
        axi_wvalid <= '0';

        axi_bready <= '0';

        axi_araddr  <= (others => '0');
        axi_arvalid <= '0';

        axi_rready <= '0';

        mi_drd  <= (others => '0');
        mi_ardy <= '0';
        mi_drdy <= '0';

        wait for RESET_TIME;
        wait for CLKPER;

        -- Read test 1
        axi_araddr  <= X"00000004";
        axi_arvalid <= '1';
        wait until axi_arready = '1';
        mi_drd      <= X"DEADBEEF";
        wait for CLKPER;
        axi_arvalid <= '0';
        axi_rready  <= '1';
        mi_ardy     <= '1';
        mi_drdy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        mi_drdy     <= '0';
        mi_drd      <= (others => '0');
        wait for CLKPER;
        axi_rready  <= '0';
        wait for 2*CLKPER;

        -- Read test 2
        axi_araddr  <= X"00000008";
        axi_arvalid <= '1';
        wait until axi_arready = '1';
        mi_drd      <= X"DEADBABE";
        wait for CLKPER;
        axi_arvalid <= '0';
        axi_rready  <= '1';
        mi_ardy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        wait for CLKPER;
        mi_drdy     <= '1';
        wait for CLKPER;
        mi_drdy     <= '0';
        mi_drd      <= (others => '0');
        wait for CLKPER;
        axi_rready  <= '0';
        wait for 2*CLKPER;

        -- Read test 3
        axi_araddr  <= X"0000000C";
        axi_arvalid <= '1';
        wait until axi_arready = '1';
        mi_drd      <= X"DEADBEEF";
        wait for CLKPER;
        axi_arvalid <= '0';
        axi_rready  <= '1';
        wait for 2*CLKPER;
        mi_ardy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        wait for CLKPER;
        mi_drdy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        mi_drdy     <= '0';
        mi_drd      <= (others => '0');
        wait for CLKPER;
        axi_rready  <= '0';
        wait for 2*CLKPER;

        -- Write test 1
        axi_awaddr  <= X"00000010";
        axi_awvalid <= '1';
        wait until axi_awready = '1';
        wait for CLKPER;
        axi_awvalid <= '0';
        axi_wdata   <= X"DEADBEEF";
        axi_wvalid  <= '1';
        wait for CLKPER;
        axi_wdata   <= (others => '0');
        axi_wvalid  <= '0';
        axi_bready  <= '1';
        mi_ardy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        wait for 2*CLKPER;
        axi_bready  <= '0';
        wait for 2*CLKPER;

        -- Write test 2
        axi_awaddr  <= X"00000014";
        axi_awvalid <= '1';
        wait until axi_awready = '1';
        wait for CLKPER;
        axi_awvalid <= '0';
        axi_wdata   <= X"DEADBEEF";
        axi_wvalid  <= '1';
        wait for CLKPER;
        axi_wdata   <= (others => '0');
        axi_wvalid  <= '0';
        axi_bready  <= '1';
        wait for CLKPER;
        mi_ardy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        wait for CLKPER;
        axi_bready  <= '0';
        wait for 2*CLKPER;

        -- Write test 3
        axi_awaddr  <= X"00000018";
        axi_awvalid <= '1';
        axi_wdata   <= X"DEADBEEF";
        axi_wvalid  <= '1';
        wait until axi_awready = '1';
        wait for CLKPER;
        axi_awvalid <= '0';
        wait for CLKPER;
        axi_wdata   <= (others => '0');
        axi_wvalid  <= '0';
        wait for CLKPER;
        axi_bready  <= '1';
        mi_ardy     <= '1';
        wait for CLKPER;
        mi_ardy     <= '0';
        wait for 2*CLKPER;
        axi_bready  <= '0';
        wait for 2*CLKPER;

        wait;

    end process;
end architecture;
