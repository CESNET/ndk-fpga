-- bmc_wrap.vhd : Wrapper of Bittware BMC
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

architecture FULL of BMC_WRAP is

    constant bmc_mi_addr_base : slv_array_t(2-1 downto 0)(32-1 downto 0) := (X"00000100", X"00000000");

    signal axi_mi_addr      : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_dwr       : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_be        : slv_array_t (2-1 downto 0)(32/8-1 downto 0);
    signal axi_mi_rd        : std_logic_vector(2-1 downto 0);
    signal axi_mi_wr        : std_logic_vector(2-1 downto 0);
    signal axi_mi_drd       : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_ardy      : std_logic_vector(2-1 downto 0);
    signal axi_mi_drdy      : std_logic_vector(2-1 downto 0);

    signal axi_awid         : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_awaddr       : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_awlen        : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_awsize       : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal axi_awburst      : slv_array_t(2-1 downto 0)(2-1 downto 0);
    signal axi_awprot       : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal axi_awvalid      : std_logic_vector(2-1 downto 0);
    signal axi_awready      : std_logic_vector(2-1 downto 0);
    signal axi_wdata        : slv_array_t(2-1 downto 0)(32-1 downto 0);
    signal axi_wstrb        : slv_array_t(2-1 downto 0)((32/8)-1 downto 0);
    signal axi_wvalid       : std_logic_vector(2-1 downto 0);
    signal axi_wready       : std_logic_vector(2-1 downto 0);
    signal axi_bid          : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_bresp        : slv_array_t(2-1 downto 0)(2-1 downto 0);
    signal axi_bvalid       : std_logic_vector(2-1 downto 0);
    signal axi_bready       : std_logic_vector(2-1 downto 0);
    signal axi_arid         : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_araddr       : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_arlen        : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_arsize       : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal axi_arburst      : slv_array_t(2-1 downto 0)(2-1 downto 0);
    signal axi_arprot       : slv_array_t(2-1 downto 0)(3-1 downto 0);
    signal axi_arvalid      : std_logic_vector(2-1 downto 0);
    signal axi_arready      : std_logic_vector(2-1 downto 0);
    signal axi_rid          : slv_array_t(2-1 downto 0)(8-1 downto 0);
    signal axi_rdata        : slv_array_t(2-1 downto 0)(32-1 downto 0);
    signal axi_rresp        : slv_array_t(2-1 downto 0)(2-1 downto 0);
    signal axi_rlast        : std_logic_vector(2-1 downto 0);
    signal axi_rvalid       : std_logic_vector(2-1 downto 0);
    signal axi_rready       : std_logic_vector(2-1 downto 0);

begin

    mi_splitter_gls_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH => 32,
        DATA_WIDTH => 32,
        META_WIDTH => 0,
        PORTS      => 2,
        PIPE_OUT   => (others => false),
        ADDR_BASES => 2,
        ADDR_MASK  => X"00000100",
        ADDR_BASE  => bmc_mi_addr_base,
        DEVICE     => DEVICE
        )
    port map(
        CLK     => CLK,
        RESET   => RESET,

        RX_DWR  => MI_DWR,
        RX_ADDR => MI_ADDR,
        RX_BE   => MI_BE,
        RX_RD   => MI_RD,
        RX_WR   => MI_WR,
        RX_ARDY => MI_ARDY,
        RX_DRD  => MI_DRD,
        RX_DRDY => MI_DRDY,

        TX_DWR  => axi_mi_dwr,
        TX_ADDR => axi_mi_addr,
        TX_BE   => axi_mi_be,
        TX_RD   => axi_mi_rd,
        TX_WR   => axi_mi_wr,
        TX_ARDY => axi_mi_ardy,
        TX_DRD  => axi_mi_drd,
        TX_DRDY => axi_mi_drdy
    );

    mi2axi_g : for i in 0 to 2-1 generate
        mi2axi: entity work.MI2AXI4
        generic map(
            AXI_DATA_WIDTH => 32,
            ADDR_WIDTH     => 8
        )
        port map(
            CLK         => CLK,
            RESET       => RESET,

            MI_DWR      => axi_mi_dwr(i),
            MI_ADDR     => axi_mi_addr(i)(7 downto 0),
            MI_RD       => axi_mi_rd(i),
            MI_WR       => axi_mi_wr(i),
            MI_BE       => axi_mi_be(i),
            MI_DRD      => axi_mi_drd(i),
            MI_ARDY     => axi_mi_ardy(i),
            MI_DRDY     => axi_mi_drdy(i),

            AXI_AWID    => axi_awid(i),
            AXI_AWADDR  => axi_awaddr(i),
            AXI_AWLEN   => axi_awlen(i),
            AXI_AWSIZE  => axi_awsize(i),
            AXI_AWBURST => axi_awburst(i),
            AXI_AWPROT  => axi_awprot(i),
            AXI_AWVALID => axi_awvalid(i),
            AXI_AWREADY => axi_awready(i),
            AXI_WDATA   => axi_wdata(i),
            AXI_WSTRB   => axi_wstrb(i),
            AXI_WVALID  => axi_wvalid(i),
            AXI_WREADY  => axi_wready(i),
            AXI_BID     => axi_bid(i),
            AXI_BRESP   => axi_bresp(i),
            AXI_BVALID  => axi_bvalid(i),
            AXI_BREADY  => axi_bready(i),
            AXI_ARID    => axi_arid(i),
            AXI_ARADDR  => axi_araddr(i),
            AXI_ARLEN   => axi_arlen(i),
            AXI_ARSIZE  => axi_arsize(i),
            AXI_ARBURST => axi_arburst(i),
            AXI_ARPROT  => axi_arprot(i),
            AXI_ARVALID => axi_arvalid(i),
            AXI_ARREADY => axi_arready(i),
            AXI_RID     => axi_rid(i),
            AXI_RDATA   => axi_rdata(i),
            AXI_RRESP   => axi_rresp(i),
            AXI_RLAST   => axi_rlast(i),
            AXI_RVALID  => axi_rvalid(i),
            AXI_RREADY  => axi_rready(i)
        );
    end generate;

    bmc_3v0_top_i : entity work.bmc_3v0_top
    port map (
        -- Host0 AXI Interface - MCTP
        host0_aclk              => CLK,
        host0_areset            => RESET,
        host0_awaddr            => axi_awaddr(0),
        host0_awvalid           => axi_awvalid(0),
        host0_awready           => axi_awready(0),
        host0_awprot            => axi_awprot(0),
        host0_wdata             => axi_wdata(0),
        host0_wstrb             => axi_wstrb(0),
        host0_wvalid            => axi_wvalid(0),
        host0_wready            => axi_wready(0),
        host0_bresp             => axi_bresp(0),
        host0_bvalid            => axi_bvalid(0),
        host0_bready            => axi_bready(0),
        host0_araddr            => axi_araddr(0),
        host0_arvalid           => axi_arvalid(0),
        host0_arready           => axi_arready(0),
        host0_arprot            => axi_arprot(0),
        host0_rdata             => axi_rdata(0),
        host0_rresp             => axi_rresp(0),
        host0_rvalid            => axi_rvalid(0),
        host0_rready            => axi_rready(0),
        -- Host1 AXI Interface - I2C
        host1_aclk              => CLK,
        host1_areset            => RESET,
        host1_awaddr            => axi_awaddr(1),
        host1_awvalid           => axi_awvalid(1),
        host1_awready           => axi_awready(1),
        host1_awprot            => axi_awprot(1),
        host1_wdata             => axi_wdata(1),
        host1_wstrb             => axi_wstrb(1),
        host1_wvalid            => axi_wvalid(1),
        host1_wready            => axi_wready(1),
        host1_bresp             => axi_bresp(1),
        host1_bvalid            => axi_bvalid(1),
        host1_bready            => axi_bready(1),
        host1_araddr            => axi_araddr(1),
        host1_arvalid           => axi_arvalid(1),
        host1_arready           => axi_arready(1),
        host1_arprot            => axi_arprot(1),
        host1_rdata             => axi_rdata(1),
        host1_rresp             => axi_rresp(1),
        host1_rvalid            => axi_rvalid(1),
        host1_rready            => axi_rready(1),
        -- Capability ROM AXI Interface
        cap_rom_aclk              => CLK,
        cap_rom_areset            => RESET,
        cap_rom_awaddr            => (others => '0'),
        cap_rom_awvalid           => '0',
        cap_rom_awready           => open,
        cap_rom_awprot            => (others=> '0'),
        cap_rom_wdata             => (others => '0'),
        cap_rom_wstrb             => (others => '0'),
        cap_rom_wvalid            => '0',
        cap_rom_wready            => open,
        cap_rom_bresp             => open,
        cap_rom_bvalid            => open,
        cap_rom_bready            => '1',
        cap_rom_araddr            => (others => '0'),
        cap_rom_arvalid           => '0',
        cap_rom_arready           => open,
        cap_rom_arprot            => (others => '0'),
        cap_rom_rdata             => open,
        cap_rom_rresp             => open,
        cap_rom_rvalid            => open,
        cap_rom_rready            => '1',
        -- SPI System Clock and Reset
        spi_sys_clk             => CLK,
        spi_sys_reset           => RESET,
        -- SPI Interface
        bmc_if_ready_n          => BMC_IF_PRESENT_N,
        spi_slv_sclk            => FPGA_IG_SPI_SCK,
        spi_slv_ss_n            => FPGA_IG_SPI_PCS0,
        spi_slv_mosi            => FPGA_IG_SPI_MOSI,
        spi_slv_miso            => FPGA_IG_SPI_MISO,
        f2b_irq_n               => FPGA_TO_BMC_IRQ,
        spi_mst_sclk            => FPGA_EG_SPI_SCK,
        spi_mst_ss_n            => FPGA_EG_SPI_PCS0,
        spi_mst_mosi            => FPGA_EG_SPI_MOSI,
        spi_mst_miso            => FPGA_EG_SPI_MISO,
        b2f_irq_n               => BMC_TO_FPGA_IRQ,
        -- Telemetry Vectors
        telemetry_clk           => CLK,
        telemetry_reset         => RESET,

        qsfpdd0_rst_n           => QSFPDD0_RST_N,
        qsfpdd0_lpmode          => QSFPDD0_LPMODE,
        qsfpdd0_int_n           => QSFPDD0_INT_N,
        qsfpdd0_present_n       => QSFPDD0_PRESENT_N
    );

end architecture;
