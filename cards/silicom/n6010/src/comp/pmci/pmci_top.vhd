-- pmci_top.vhd : Wrapper of N6010 PMCI IP
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity PMCI_TOP is
    generic(
        -- Target device
        DEVICE : string := "AGILEX"
    );
    port(
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK                      : in  std_logic;
        RESET                    : in  std_logic;

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR                   : in  std_logic_vector(32-1 downto 0);
        MI_ADDR                  : in  std_logic_vector(32-1 downto 0);
        MI_RD                    : in  std_logic;
        MI_WR                    : in  std_logic;
        MI_BE                    : in  std_logic_vector((32/8)-1 downto 0);
        MI_DRD                   : out std_logic_vector(32-1 downto 0);
        MI_ARDY                  : out std_logic;
        MI_DRDY                  : out std_logic;
        
        -- =====================================================================
        -- BMC interface
        -- =====================================================================
        QSPI_DCLK                : out   std_logic;
        QSPI_NCS                 : out   std_logic;
        QSPI_DATA                : inout std_logic_vector(4-1 downto 0);
        NCSI_RBT_NCSI_CLK        : in    std_logic;
        NCSI_RBT_NCSI_TXD        : in    std_logic_vector(2-1 downto 0);
        NCSI_RBT_NCSI_TX_EN      : in    std_logic;
        NCSI_RBT_NCSI_RXD        : out   std_logic_vector(2-1 downto 0);
        NCSI_RBT_NCSI_CRS_DV     : out   std_logic;
        NCSI_RBT_NCSI_ARB_IN     : in    std_logic;
        NCSI_RBT_NCSI_ARB_OUT    : out   std_logic;
        M10_GPIO_FPGA_USR_100M   : in    std_logic;
        M10_GPIO_FPGA_M10_HB     : in    std_logic;
        M10_GPIO_M10_SEU_ERROR   : in    std_logic;
        M10_GPIO_FPGA_THERM_SHDN : out   std_logic;
        M10_GPIO_FPGA_SEU_ERROR  : out   std_logic;
        SPI_INGRESS_SCLK         : out   std_logic;
        SPI_INGRESS_CSN          : out   std_logic;
        SPI_INGRESS_MISO         : in    std_logic;
        SPI_INGRESS_MOSI         : out   std_logic;
        SPI_EGRESS_MOSI          : in    std_logic;
        SPI_EGRESS_CSN           : in    std_logic;
        SPI_EGRESS_SCLK          : in    std_logic;
        SPI_EGRESS_MISO          : out   std_logic
    );

end entity;

architecture FULL of PMCI_TOP is

    component pmci_ss is
    port (
        axi_mstr_awid                                              : out std_logic_vector(8-1 downto 0);
        axi_mstr_awaddr                                            : out std_logic_vector(21-1 downto 0);
        axi_mstr_awprot                                            : out std_logic_vector(3-1 downto 0);
        axi_mstr_awvalid                                           : out std_logic;
        axi_mstr_awready                                           : in  std_logic;
        axi_mstr_wdata                                             : out std_logic_vector(64-1 downto 0);
        axi_mstr_wstrb                                             : out std_logic_vector((64/8)-1 downto 0);
        axi_mstr_wlast                                             : out std_logic;
        axi_mstr_wvalid                                            : out std_logic;
        axi_mstr_wready                                            : in  std_logic;
        axi_mstr_bid                                               : in  std_logic_vector(8-1 downto 0);
        axi_mstr_bresp                                             : in  std_logic_vector(2-1 downto 0);    
        axi_mstr_bvalid                                            : in  std_logic;
        axi_mstr_bready                                            : out std_logic;
        axi_mstr_arid                                              : out std_logic_vector(8-1 downto 0);
        axi_mstr_araddr                                            : out std_logic_vector(21-1 downto 0);
        axi_mstr_arprot                                            : out std_logic_vector(3-1 downto 0);
        axi_mstr_arvalid                                           : out std_logic;
        axi_mstr_arready                                           : in  std_logic;
        axi_mstr_rid                                               : in  std_logic_vector(8-1 downto 0);
        axi_mstr_rdata                                             : in  std_logic_vector(64-1 downto 0);
        axi_mstr_rresp                                             : in  std_logic_vector(2-1 downto 0);
        axi_mstr_rvalid                                            : in  std_logic;
        axi_mstr_rready                                            : out std_logic;

        axi_slave_awid                                             : in  std_logic_vector(8-1 downto 0);
        axi_slave_awaddr                                           : in  std_logic_vector(17-1 downto 0);
        axi_slave_awlen                                            : in  std_logic_vector(8-1 downto 0);
        axi_slave_awsize                                           : in  std_logic_vector(3-1 downto 0);
        axi_slave_awburst                                          : in  std_logic_vector(2-1 downto 0);
        axi_slave_awprot                                           : in  std_logic_vector(3-1 downto 0);
        axi_slave_awvalid                                          : in  std_logic;
        axi_slave_awready                                          : out std_logic;
        axi_slave_wdata                                            : in  std_logic_vector(64-1 downto 0);
        axi_slave_wstrb                                            : in  std_logic_vector((64/8)-1 downto 0);
        axi_slave_wvalid                                           : in  std_logic;
        axi_slave_wready                                           : out std_logic;
        axi_slave_bid                                              : out std_logic_vector(8-1 downto 0);
        axi_slave_bresp                                            : out std_logic_vector(2-1 downto 0);    
        axi_slave_bvalid                                           : out std_logic;
        axi_slave_bready                                           : in  std_logic;
        axi_slave_arid                                             : in  std_logic_vector(8-1 downto 0);
        axi_slave_araddr                                           : in  std_logic_vector(17-1 downto 0);
        axi_slave_arlen                                            : in  std_logic_vector(8-1 downto 0);
        axi_slave_arsize                                           : in  std_logic_vector(3-1 downto 0);
        axi_slave_arburst                                          : in  std_logic_vector(2-1 downto 0);
        axi_slave_arprot                                           : in  std_logic_vector(3-1 downto 0);
        axi_slave_arvalid                                          : in  std_logic;
        axi_slave_arready                                          : out std_logic;
        axi_slave_rid                                              : out std_logic_vector(8-1 downto 0);
        axi_slave_rdata                                            : out std_logic_vector(64-1 downto 0);
        axi_slave_rresp                                            : out std_logic_vector(2-1 downto 0);
        axi_slave_rlast                                            : out std_logic;
        axi_slave_rvalid                                           : out std_logic;
        axi_slave_rready                                           : in  std_logic;

        clk_clk                                                    : in    std_logic;
        qspi_dclk                                                  : out   std_logic;
        qspi_ncs                                                   : out   std_logic;
        qspi_data                                                  : inout std_logic_vector(4-1 downto 0);
        ncsi_rbt_ncsi_clk                                          : in    std_logic;
        ncsi_rbt_ncsi_txd                                          : in    std_logic_vector(2-1 downto 0);
        ncsi_rbt_ncsi_tx_en                                        : in    std_logic;
        ncsi_rbt_ncsi_rxd                                          : out   std_logic_vector(2-1 downto 0);
        ncsi_rbt_ncsi_crs_dv                                       : out   std_logic;
        ncsi_rbt_ncsi_arb_in                                       : in    std_logic;
        ncsi_rbt_ncsi_arb_out                                      : out   std_logic;
        m10_gpio_fpga_usr_100m                                     : in    std_logic;
        m10_gpio_fpga_m10_hb                                       : in    std_logic;
        m10_gpio_m10_seu_error                                     : in    std_logic;
        m10_gpio_fpga_therm_shdn                                   : out   std_logic;
        m10_gpio_fpga_seu_error                                    : out   std_logic;
        reset_reset                                                : in    std_logic;
        spi_ingress_sclk                                           : out   std_logic;
        spi_ingress_csn                                            : out   std_logic;
        spi_ingress_miso                                           : in    std_logic;
        spi_ingress_mosi                                           : out   std_logic;
        spi_egress_mosi_to_the_spislave_inst_for_spichain          : in    std_logic;
        spi_egress_nss_to_the_spislave_inst_for_spichain           : in    std_logic;
        spi_egress_sclk_to_the_spislave_inst_for_spichain          : in    std_logic;
        spi_egress_miso_to_and_from_the_spislave_inst_for_spichain : out   std_logic
    );
    end component;

    signal axi_mstr_awid    : std_logic_vector(8-1 downto 0);
    signal axi_mstr_awaddr  : std_logic_vector(21-1 downto 0);
    signal axi_mstr_awprot  : std_logic_vector(3-1 downto 0);
    signal axi_mstr_awvalid : std_logic;
    signal axi_mstr_awready : std_logic;
    signal axi_mstr_wdata   : std_logic_vector(64-1 downto 0);
    signal axi_mstr_wstrb   : std_logic_vector((64/8)-1 downto 0);
    signal axi_mstr_wlast   : std_logic;
    signal axi_mstr_wvalid  : std_logic;
    signal axi_mstr_wready  : std_logic;
    signal axi_mstr_bid     : std_logic_vector(8-1 downto 0);
    signal axi_mstr_bresp   : std_logic_vector(2-1 downto 0);    
    signal axi_mstr_bvalid  : std_logic;
    signal axi_mstr_bready  : std_logic;
    signal axi_mstr_arid    : std_logic_vector(8-1 downto 0);
    signal axi_mstr_araddr  : std_logic_vector(21-1 downto 0);
    signal axi_mstr_arprot  : std_logic_vector(3-1 downto 0);
    signal axi_mstr_arvalid : std_logic;
    signal axi_mstr_arready : std_logic;
    signal axi_mstr_rid     : std_logic_vector(8-1 downto 0);
    signal axi_mstr_rdata   : std_logic_vector(64-1 downto 0);
    signal axi_mstr_rresp   : std_logic_vector(2-1 downto 0);
    signal axi_mstr_rvalid  : std_logic;
    signal axi_mstr_rready  : std_logic;

    signal csr_awid         : std_logic_vector(8-1 downto 0);
    signal csr_awaddr       : std_logic_vector(32-1 downto 0);
    signal csr_awlen        : std_logic_vector(8-1 downto 0);
    signal csr_awsize       : std_logic_vector(3-1 downto 0);
    signal csr_awburst      : std_logic_vector(2-1 downto 0);
    signal csr_awprot       : std_logic_vector(3-1 downto 0);
    signal csr_awvalid      : std_logic;
    signal csr_awready      : std_logic;
    signal csr_wdata        : std_logic_vector(64-1 downto 0);
    signal csr_wstrb        : std_logic_vector((64/8)-1 downto 0);
    signal csr_wvalid       : std_logic;
    signal csr_wready       : std_logic;
    signal csr_bid          : std_logic_vector(8-1 downto 0);
    signal csr_bresp        : std_logic_vector(2-1 downto 0);    
    signal csr_bvalid       : std_logic;
    signal csr_bready       : std_logic;
    signal csr_arid         : std_logic_vector(8-1 downto 0);
    signal csr_araddr       : std_logic_vector(32-1 downto 0);
    signal csr_arlen        : std_logic_vector(8-1 downto 0);
    signal csr_arsize       : std_logic_vector(3-1 downto 0);
    signal csr_arburst      : std_logic_vector(2-1 downto 0);
    signal csr_arprot       : std_logic_vector(3-1 downto 0);
    signal csr_arvalid      : std_logic;
    signal csr_arready      : std_logic;
    signal csr_rid          : std_logic_vector(8-1 downto 0);
    signal csr_rdata        : std_logic_vector(64-1 downto 0);
    signal csr_rresp        : std_logic_vector(2-1 downto 0);
    signal csr_rlast        : std_logic;
    signal csr_rvalid       : std_logic;
    signal csr_rready       : std_logic;

begin

    mi2axi4_i : entity work.MI2AXI4
    generic map(
        MI_DATA_WIDTH  => 32,
        AXI_DATA_WIDTH => 64,
        ADDR_WIDTH     => 32,
        ADDR_MASK      => X"00000FFF",
        DEVICE         => DEVICE
    ) port map(
        CLK         => CLK,
        RESET       => RESET,

        MI_DWR      => MI_DWR,
        MI_ADDR     => MI_ADDR,
        MI_RD       => MI_RD,
        MI_WR       => MI_WR,
        MI_BE       => MI_BE,
        MI_DRD      => MI_DRD,
        MI_ARDY     => MI_ARDY,
        MI_DRDY     => MI_DRDY,

        AXI_AWID    => csr_awid,
        AXI_AWADDR  => csr_awaddr,
        AXI_AWLEN   => csr_awlen,
        AXI_AWSIZE  => csr_awsize,
        AXI_AWBURST => csr_awburst,
        AXI_AWPROT  => csr_awprot,
        AXI_AWVALID => csr_awvalid,
        AXI_AWREADY => csr_awready,
        AXI_WDATA   => csr_wdata,
        AXI_WSTRB   => csr_wstrb,
        AXI_WVALID  => csr_wvalid,
        AXI_WREADY  => csr_wready,
        AXI_BID     => csr_bid,
        AXI_BRESP   => csr_bresp,
        AXI_BVALID  => csr_bvalid,
        AXI_BREADY  => csr_bready,
        AXI_ARID    => csr_arid,
        AXI_ARADDR  => csr_araddr,
        AXI_ARLEN   => csr_arlen,
        AXI_ARSIZE  => csr_arsize,
        AXI_ARBURST => csr_arburst,
        AXI_ARPROT  => csr_arprot,
        AXI_ARVALID => csr_arvalid,
        AXI_ARREADY => csr_arready,
        AXI_RID     => csr_rid,
        AXI_RDATA   => csr_rdata,
        AXI_RRESP   => csr_rresp,
        AXI_RLAST   => csr_rlast,
        AXI_RVALID  => csr_rvalid,
        AXI_RREADY  => csr_rready
    );

    pmci_i : component pmci_ss
    port map(
        axi_mstr_awid                                              => axi_mstr_awid,
        axi_mstr_awaddr                                            => axi_mstr_awaddr,
        axi_mstr_awprot                                            => axi_mstr_awprot,
        axi_mstr_awvalid                                           => axi_mstr_awvalid,
        axi_mstr_awready                                           => axi_mstr_awready,
        axi_mstr_wdata                                             => axi_mstr_wdata,
        axi_mstr_wstrb                                             => axi_mstr_wstrb,
        axi_mstr_wlast                                             => axi_mstr_wlast,
        axi_mstr_wvalid                                            => axi_mstr_wvalid,
        axi_mstr_wready                                            => axi_mstr_wready,
        axi_mstr_bid                                               => axi_mstr_bid,
        axi_mstr_bresp                                             => axi_mstr_bresp,
        axi_mstr_bvalid                                            => axi_mstr_bvalid,
        axi_mstr_bready                                            => axi_mstr_bready,
        axi_mstr_arid                                              => axi_mstr_arid,
        axi_mstr_araddr                                            => axi_mstr_araddr,
        axi_mstr_arprot                                            => axi_mstr_arprot,
        axi_mstr_arvalid                                           => axi_mstr_arvalid,
        axi_mstr_arready                                           => axi_mstr_arready,
        axi_mstr_rid                                               => axi_mstr_rid,
        axi_mstr_rdata                                             => axi_mstr_rdata,
        axi_mstr_rresp                                             => axi_mstr_rresp,
        axi_mstr_rvalid                                            => axi_mstr_rvalid,
        axi_mstr_rready                                            => axi_mstr_rready,
        axi_slave_awid                                             => csr_awid,
        axi_slave_awaddr                                           => csr_awaddr(17-1 downto 0),
        axi_slave_awlen                                            => csr_awlen,
        axi_slave_awsize                                           => csr_awsize,
        axi_slave_awburst                                          => csr_awburst,
        axi_slave_awprot                                           => csr_awprot,
        axi_slave_awvalid                                          => csr_awvalid,
        axi_slave_awready                                          => csr_awready,
        axi_slave_wdata                                            => csr_wdata,
        axi_slave_wstrb                                            => csr_wstrb,
        axi_slave_wvalid                                           => csr_wvalid,
        axi_slave_wready                                           => csr_wready,
        axi_slave_bid                                              => csr_bid,
        axi_slave_bresp                                            => csr_bresp,
        axi_slave_bvalid                                           => csr_bvalid,
        axi_slave_bready                                           => csr_bready,
        axi_slave_arid                                             => csr_arid,
        axi_slave_araddr                                           => csr_araddr(17-1 downto 0),
        axi_slave_arlen                                            => csr_arlen,
        axi_slave_arsize                                           => csr_arsize,
        axi_slave_arburst                                          => csr_arburst,
        axi_slave_arprot                                           => csr_arprot,
        axi_slave_arvalid                                          => csr_arvalid,
        axi_slave_arready                                          => csr_arready,
        axi_slave_rid                                              => csr_rid,
        axi_slave_rdata                                            => csr_rdata,
        axi_slave_rresp                                            => csr_rresp,
        axi_slave_rlast                                            => csr_rlast,
        axi_slave_rvalid                                           => csr_rvalid,
        axi_slave_rready                                           => csr_rready,
        clk_clk                                                    => CLK,
        qspi_dclk                                                  => QSPI_DCLK,
        qspi_ncs                                                   => QSPI_NCS,
        qspi_data                                                  => QSPI_DATA,
        ncsi_rbt_ncsi_clk                                          => NCSI_RBT_NCSI_CLK,
        ncsi_rbt_ncsi_txd                                          => NCSI_RBT_NCSI_TXD,
        ncsi_rbt_ncsi_tx_en                                        => NCSI_RBT_NCSI_TX_EN,
        ncsi_rbt_ncsi_rxd                                          => NCSI_RBT_NCSI_RXD,
        ncsi_rbt_ncsi_crs_dv                                       => NCSI_RBT_NCSI_CRS_DV,
        ncsi_rbt_ncsi_arb_in                                       => NCSI_RBT_NCSI_ARB_IN,
        ncsi_rbt_ncsi_arb_out                                      => NCSI_RBT_NCSI_ARB_OUT,
        m10_gpio_fpga_usr_100m                                     => M10_GPIO_FPGA_USR_100M,
        m10_gpio_fpga_m10_hb                                       => M10_GPIO_FPGA_M10_HB,
        m10_gpio_m10_seu_error                                     => M10_GPIO_M10_SEU_ERROR,
        m10_gpio_fpga_therm_shdn                                   => M10_GPIO_FPGA_THERM_SHDN,
        m10_gpio_fpga_seu_error                                    => M10_GPIO_FPGA_SEU_ERROR,
        reset_reset                                                => RESET,
        spi_ingress_sclk                                           => SPI_INGRESS_SCLK,
        spi_ingress_csn                                            => SPI_INGRESS_CSN,
        spi_ingress_miso                                           => SPI_INGRESS_MISO,
        spi_ingress_mosi                                           => SPI_INGRESS_MOSI,
        spi_egress_mosi_to_the_spislave_inst_for_spichain          => SPI_EGRESS_MOSI,
        spi_egress_nss_to_the_spislave_inst_for_spichain           => SPI_EGRESS_CSN,
        spi_egress_sclk_to_the_spislave_inst_for_spichain          => SPI_EGRESS_SCLK,
        spi_egress_miso_to_and_from_the_spislave_inst_for_spichain => SPI_EGRESS_MISO
    );

    axi_mstr_awready <= '1';
    axi_mstr_wready  <= '1';
    axi_mstr_bid     <= (others => '0');
    axi_mstr_bresp   <= (others => '0');
    axi_mstr_arready <= '1';
    axi_mstr_rid     <= (others => '0');
    axi_mstr_rdata   <= (others => '0');
    axi_mstr_rresp   <= (others => '0');

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                axi_mstr_bvalid <= '0';
                axi_mstr_rvalid <= '0';
            else
                axi_mstr_bvalid <= axi_mstr_wvalid;
                axi_mstr_rvalid <= axi_mstr_arvalid;
            end if;
        end if;
    end process;

end architecture;
