-- fpga.vhd: Silicom ThunderFjord fb2cdg1 card top-level entity and architecture
-- Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.ndk_fpga_top_pkg.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;

entity FPGA is
port (
    -- =========================================================================
    --  GENERAL INTERFACES
    -- =========================================================================

    -- =========================================================================
    --  GENERAL CLOCKS AND PLL STATUS SIGNALS
    -- =========================================================================
    -- 100 MHz
    SYSCLK_100_P     : in std_logic;
    FPGA_RESETN_1V2  : in std_logic;
    -- =========================================================================
    --  PCIE INTERFACES
    -- =========================================================================
    PCIE_CLK0_P            : in    std_logic;
    PCIE_CLK1_P            : in    std_logic;
    PCIE_PERST_N           : in    std_logic;
    PCIE_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE_TX_N              : out   std_logic_vector(15 downto 0);

    -- =========================================================================
    --  QSFP-DD INTERFACES - F-TILE
    -- =========================================================================
    -- First QSFP Cage
    QSFP0_MODPRS_N        : in    std_logic;
    QSFP0_INT_N           : in    std_logic;
    QSFP0_RST_N           : out   std_logic;
    QSFP0_LPMODE          : out   std_logic;
    QSFP0_I2C_SCL         : inout std_logic;
    QSFP0_I2C_SDA         : inout std_logic;

    -- 156.25 MHz
    QSFP0_REFCLK_P        : in    std_logic;
    QSFP0_RX_P            : in    std_logic_vector(7 downto 0);
    QSFP0_RX_N            : in    std_logic_vector(7 downto 0);
    QSFP0_TX_P            : out   std_logic_vector(7 downto 0);
    QSFP0_TX_N            : out   std_logic_vector(7 downto 0);

    QSFP0_LED_R           : out   std_logic;
    QSFP0_LED_G           : out   std_logic;
    QSFP0_LED_B           : out   std_logic;

    -- Second QSFP Cage
    QSFP1_MODPRS_N        : in    std_logic;
    QSFP1_INT_N           : in    std_logic;
    QSFP1_RST_N           : out   std_logic;
    QSFP1_LPMODE          : out   std_logic;
    QSFP1_I2C_SCL         : inout std_logic;
    QSFP1_I2C_SDA         : inout std_logic;

    -- 156.25 MHz
    QSFP1_REFCLK_P        : in    std_logic;
    QSFP1_RX_P            : in    std_logic_vector(7 downto 0);
    QSFP1_RX_N            : in    std_logic_vector(7 downto 0);
    QSFP1_TX_P            : out   std_logic_vector(7 downto 0);
    QSFP1_TX_N            : out   std_logic_vector(7 downto 0);

    QSFP1_LED_R           : out   std_logic;
    QSFP1_LED_G           : out   std_logic;
    QSFP1_LED_B           : out   std_logic;

    -- =========================================================================
    -- BMC INTERFACE
    -- =========================================================================
    -- QSPI interface from FPGA to Max10:
    QSPI_CSN_1V2             : out    std_logic;
    QSPI_D0                  : inout  std_logic;
    QSPI_D1                  : inout  std_logic;
    QSPI_D2                  : inout  std_logic;
    QSPI_D3                  : inout  std_logic;
    QSPI_CLK                 : out    std_logic;

    -- SPI Ingress (Seen from BMC) FPGA > MAX
    SPI_INGRESS_SCLK         : out    std_logic;
    SPI_INGRESS_CSN          : out    std_logic;
    SPI_INGRESS_MISO         : in     std_logic;
    SPI_INGRESS_MOSI         : out    std_logic;

    -- SPI Egress (Seen from BMC) MAX > FPGA
    SPI_EGRESS_MOSI          : in     std_logic;
    SPI_EGRESS_CSN           : in     std_logic;
    SPI_EGRESS_SCLK          : in     std_logic;
    SPI_EGRESS_MISO          : out    std_logic;

    -- Misc signals between FPGA and BMC:
    -- Heart beat from BMC NIOS in the BMC
    MAX_FPGA_HB_1V2          : in     std_logic;
    -- Heart beat from PMCI NIOS in this FPGA
    FPGA_MAX_HB              : out    std_logic;
    -- Single Event Upset. Active high.
    FPGA_MAX_FPGA_SEU_1V2    : out    std_logic;
    -- Thermal shutdown. Active Low
    FPGA_MAX_THRM_SHTD_N_1V2 : out    std_logic;

    -- =========================================================================
    -- HBM2e via Universal interface bus (UIB)
    -- =========================================================================
    -- NoC top
    CLK_NOC_TOP              : in std_logic;

    CLK_UIB1_FBR1_P          : in std_logic;
    HBM_TOP_CATTRIP_VIRTUAL  : in std_logic;
    HBM_TOP_TEMP_VIRTUAL     : in std_logic_vector(3-1 downto 0);
    CLK_UIB1_P               : in std_logic;

    -- -- NoC bottom
    CLK_NOC_BOTTOM           : in std_logic;

    CLK_UIB0_FBR0_P          : in std_logic;
    HBM_BOT_CATTRIP_VIRTUAL  : in std_logic;
    HBM_BOT_TEMP_VIRTUAL     : in std_logic_vector(3-1 downto 0);
    CLK_UIB0_P               : in std_logic

);
end entity;

architecture FULL of FPGA is

    constant PCIE_CLKS       : integer := 2;
    constant PCIE_CONS       : integer := 1;
    constant MISC_IN_WIDTH   : integer := 64;
    constant MISC_OUT_WIDTH  : integer := 64 + 5;
    constant ETH_LANES       : integer := 8;
    constant DEVICE          : string  := "AGILEX";

    constant HBM_PORTS_PER_MODULE: natural := HBM_PORTS/max(1,HBM_MODULES);
    constant HBM_AXI_ID_WIDTH    : natural := 7;
    constant HBM_AXI_ADDR_WIDTH  : natural := 44;
    constant HBM_AXI_LEN_WIDTH   : natural := 8;
    constant HBM_AXI_SIZE_WIDTH  : natural := 3;
    constant HBM_AXI_BURST_WIDTH : natural := 2;
    constant HBM_AXI_DATA_WIDTH  : natural := HBM_DATA_WIDTH;
    constant HBM_AXI_RESP_WIDTH  : natural := 2;
    constant HBM_AXI_PROT_WIDTH  : natural := 3;
    -- Each NoC attached port owns 1 GB of capacity ...
    constant HBM_PORT_ADDR_HBIT  : natural := 30;
    -- ... in its own address space, so the port ID is not encoded in the address.
    constant HBM_BASE_ADDR_OFFSET: natural := 0;
    constant HBM_AXI_QOS_WIDTH   : natural := 4;
    constant HBM_AXI_USER_WIDTH  : natural := 11;

    --Ethernet
    signal eth_rx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_rx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    signal eth_refclk_p           : std_logic_vector(ETH_PORTS-1 downto 0);
    signal eth_refclk_n           : std_logic_vector(ETH_PORTS-1 downto 0);

    -- HBM memory interfaces (clocked at HBM_CLK)
    subtype HBM_TOP_R is natural range HBM_PORTS_PER_MODULE - 1 downto 0;
    subtype HBM_BOT_R is natural range HBM_PORTS -1             downto HBM_PORTS_PER_MODULE;

    signal hbm_clk                : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_rst                : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_init_done          : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_awid           : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal hbm_axi_awaddr         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_awlen          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    signal hbm_axi_awsize         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_awburst        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    signal hbm_axi_awprot         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_PROT_WIDTH-1 downto 0);
    signal hbm_axi_awqos          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_QOS_WIDTH-1 downto 0);
    signal hbm_axi_awuser         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_USER_WIDTH-1 downto 0);
    signal hbm_axi_awvalid        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_awready        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wdata          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    signal hbm_axi_wstrb          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH/8-1 downto 0);
    signal hbm_axi_wlast          : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wready         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bid            : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal hbm_axi_bresp          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    signal hbm_axi_bvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bready         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arid           : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal hbm_axi_araddr         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_arlen          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_LEN_WIDTH-1 downto 0);
    signal hbm_axi_arsize         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_arburst        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_BURST_WIDTH-1 downto 0);
    signal hbm_axi_arprot         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_PROT_WIDTH-1 downto 0);
    signal hbm_axi_arqos          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_QOS_WIDTH-1 downto 0);
    signal hbm_axi_aruser         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_USER_WIDTH-1 downto 0);
    signal hbm_axi_arvalid        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arready        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rid            : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_ID_WIDTH-1 downto 0);
    signal hbm_axi_rdata          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_DATA_WIDTH-1 downto 0);
    signal hbm_axi_rresp          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_AXI_RESP_WIDTH-1 downto 0);
    signal hbm_axi_rlast          : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rready         : std_logic_vector(HBM_PORTS-1 downto 0);

    -- Boot
    signal boot_mi_clk            : std_logic;
    signal boot_mi_reset          : std_logic;
    signal boot_mi_dwr            : std_logic_vector(31 downto 0);
    signal boot_mi_addr           : std_logic_vector(31 downto 0);
    signal boot_mi_rd             : std_logic;
    signal boot_mi_wr             : std_logic;
    signal boot_mi_be             : std_logic_vector(3 downto 0);
    signal boot_mi_drd            : std_logic_vector(31 downto 0);
    signal boot_mi_ardy           : std_logic;
    signal boot_mi_drdy           : std_logic;

begin

    QSFP0_LED_B <= '0';
    QSFP1_LED_B <= '0';

    -- QSFP MAPPING ------------------------------------------------------------
    eth_refclk_p <= QSFP1_REFCLK_P & QSFP0_REFCLK_P;
    eth_refclk_n <= (others => '0'); -- Quartus will handle the connection itself

    eth_rx_p <= QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP1_RX_N & QSFP0_RX_N;

    QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);

    ag_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 10.0,
        PLL_MULT_F              => 12.0,
        PLL_MASTER_DIV          => 1,
        PLL_OUT0_DIV_F          => 3.0,
        PLL_OUT1_DIV            => 4,
        PLL_OUT2_DIV            => 6,
        PLL_OUT3_DIV            => 12,

        HBM_MODULES             => HBM_MODULES,
        HBM_PORTS               => HBM_PORTS,
        HBM_ID_WIDTH            => HBM_AXI_ID_WIDTH,
        HBM_ADDR_WIDTH          => HBM_AXI_ADDR_WIDTH,
        HBM_LEN_WIDTH           => HBM_AXI_LEN_WIDTH,
        HBM_SIZE_WIDTH          => HBM_AXI_SIZE_WIDTH,
        HBM_BURST_WIDTH         => HBM_AXI_BURST_WIDTH,
        HBM_DATA_WIDTH          => HBM_AXI_DATA_WIDTH,
        HBM_RESP_WIDTH          => HBM_AXI_RESP_WIDTH,
        HBM_PORT_ADDR_HBIT      => HBM_PORT_ADDR_HBIT,
        HBM_BASE_ADDR_OFFSET    => HBM_BASE_ADDR_OFFSET,
        HBM_PROT_WIDTH          => HBM_AXI_PROT_WIDTH,
        HBM_QOS_WIDTH           => HBM_AXI_QOS_WIDTH,
        HBM_USER_WIDTH          => HBM_AXI_USER_WIDTH,

        PCIE_CONS               => PCIE_CONS,
        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_LEDS           => 1,
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => ETH_PORTS,
        QSFP_I2C_PORTS          => ETH_PORTS,

        MEM_PORTS               => 0,
        -- MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH,
        -- MEM_DATA_WIDTH          => MEM_DATA_WIDTH,
        -- MEM_BURST_WIDTH         => MEM_BURST_WIDTH,
        -- AMM_FREQ_KHZ            => AMM_FREQ_KHZ,

        STATUS_LEDS             => 2,

        MISC_IN_WIDTH           => MISC_IN_WIDTH,
        MISC_OUT_WIDTH          => MISC_OUT_WIDTH,

        BOARD                   => CARD_NAME,
        DEVICE                  => DEVICE,

        PCIE_ENDPOINTS          => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE      => PCIE_MOD_ARCH,
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE
    )
    port map(
        SYSCLK                  => SYSCLK_100_P,
        SYSRST                  => '0',

        PCIE_SYSCLK_P           => PCIE_CLK1_P & PCIE_CLK0_P,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N           => (others => PCIE_PERST_N),

        PCIE_RX_P               => PCIE_RX_P,
        PCIE_RX_N               => PCIE_RX_N,
        PCIE_TX_P               => PCIE_TX_P,
        PCIE_TX_N               => PCIE_TX_N,

        ETH_REFCLK_P            => eth_refclk_p,
        ETH_REFCLK_N            => eth_refclk_n,
        ETH_RX_P                => eth_rx_p,
        ETH_RX_N                => eth_rx_n,
        ETH_TX_P                => eth_tx_p,
        ETH_TX_N                => eth_tx_n,

        ETH_LED_R(0)            => QSFP0_LED_R,
        ETH_LED_R(1)            => QSFP1_LED_R,

        ETH_LED_G(0)            => QSFP0_LED_G,
        ETH_LED_G(1)            => QSFP1_LED_G,

        QSFP_I2C_SCL(0)         => QSFP0_I2C_SCL,
        QSFP_I2C_SCL(1)         => QSFP1_I2C_SCL,

        QSFP_I2C_SDA(0)         => QSFP0_I2C_SDA,
        QSFP_I2C_SDA(1)         => QSFP1_I2C_SDA,

        -- QSFP_MODSEL_N(0)        => open, --N/A
        -- QSFP_MODSEL_N(1)        => open, --N/A

        QSFP_LPMODE(0)          => QSFP0_LPMODE,
        QSFP_LPMODE(1)          => QSFP1_LPMODE,

        QSFP_RESET_N(0)         => QSFP0_RST_N,
        QSFP_RESET_N(1)         => QSFP1_RST_N,

        QSFP_MODPRS_N(0)        => QSFP0_MODPRS_N,
        QSFP_MODPRS_N(1)        => QSFP1_MODPRS_N,

        QSFP_INT_N(0)           => QSFP0_INT_N,
        QSFP_INT_N(1)           => QSFP1_INT_N,

        MEM_CLK                 => (others => '0'),
        MEM_RST                 => (others => '0'),

        MEM_AVMM_READY          => (others => '0'),
        MEM_AVMM_READ           => open,
        MEM_AVMM_WRITE          => open,
        MEM_AVMM_ADDRESS        => open,
        MEM_AVMM_BURSTCOUNT     => open,
        MEM_AVMM_WRITEDATA      => open,
        MEM_AVMM_READDATA       => (others => (others => '1')),
        MEM_AVMM_READDATAVALID  => (others => '0'),

        EMIF_RST_REQ            => open,
        EMIF_RST_DONE           => (others => '0'),
        EMIF_ECC_USR_INT        => (others => '0'),
        EMIF_CAL_SUCCESS        => (others => '0'),
        EMIF_CAL_FAIL           => (others => '0'),

        STATUS_LED_G            => open,
        STATUS_LED_R            => open,

        PCIE_CLK                => open,
        PCIE_RESET              => open,

        HBM_CLK                 => hbm_clk,
        HBM_RESET               => hbm_rst,
        HBM_INIT_DONE           => hbm_init_done,

        -- Warning! HBM does not contain a reorder buffer.
        -- Transactions can be sent in any order, provided that the AXI_ID is not the same number.
        HBM_AXI_ARID            => hbm_axi_arid,
        HBM_AXI_ARADDR          => hbm_axi_araddr,
        HBM_AXI_ARLEN           => hbm_axi_arlen,
        HBM_AXI_ARSIZE          => hbm_axi_arsize,
        HBM_AXI_ARBURST         => hbm_axi_arburst,
        HBM_AXI_ARVALID         => hbm_axi_arvalid,
        HBM_AXI_ARREADY         => hbm_axi_arready,

        HBM_AXI_RID             => hbm_axi_rid,
        HBM_AXI_RDATA           => hbm_axi_rdata,
        HBM_AXI_RRESP           => hbm_axi_rresp,
        HBM_AXI_RLAST           => hbm_axi_rlast,
        HBM_AXI_RVALID          => hbm_axi_rvalid,
        HBM_AXI_RREADY          => hbm_axi_rready,

        HBM_AXI_AWID            => hbm_axi_awid,
        HBM_AXI_AWADDR          => hbm_axi_awaddr,
        HBM_AXI_AWLEN           => hbm_axi_awlen,
        HBM_AXI_AWSIZE          => hbm_axi_awsize,
        HBM_AXI_AWBURST         => hbm_axi_awburst,
        HBM_AXI_AWVALID         => hbm_axi_awvalid,
        HBM_AXI_AWREADY         => hbm_axi_awready,

        HBM_AXI_WDATA           => hbm_axi_wdata,
        HBM_AXI_WSTRB           => hbm_axi_wstrb,
        HBM_AXI_WLAST           => hbm_axi_wlast,
        HBM_AXI_WVALID          => hbm_axi_wvalid,
        HBM_AXI_WREADY          => hbm_axi_wready,

        HBM_AXI_BID             => hbm_axi_bid,
        HBM_AXI_BRESP           => hbm_axi_bresp,
        HBM_AXI_BVALID          => hbm_axi_bvalid,
        HBM_AXI_BREADY          => hbm_axi_bready,

        BOOT_MI_CLK            => boot_mi_clk,
        BOOT_MI_RESET          => boot_mi_reset,
        BOOT_MI_DWR            => boot_mi_dwr,
        BOOT_MI_ADDR           => boot_mi_addr,
        BOOT_MI_RD             => boot_mi_rd,
        BOOT_MI_WR             => boot_mi_wr,
        BOOT_MI_BE             => boot_mi_be,
        BOOT_MI_DRD            => boot_mi_drd,
        BOOT_MI_ARDY           => boot_mi_ardy,
        BOOT_MI_DRDY           => boot_mi_drdy,

        MISC_IN                 => (others => '0'),
        MISC_OUT                => open
    );

    -- BMC controller
    bmc_wrap_i : entity work.BMC_WRAP
    generic map(
        DEVICE => DEVICE
    ) port map(
        CLK                      => boot_mi_clk,
        RESET                    => boot_mi_reset,

        MI_DWR                   => boot_mi_dwr,
        MI_ADDR                  => boot_mi_addr,
        MI_RD                    => boot_mi_rd,
        MI_WR                    => boot_mi_wr,
        MI_BE                    => boot_mi_be,
        MI_DRD                   => boot_mi_drd,
        MI_ARDY                  => boot_mi_ardy,
        MI_DRDY                  => boot_mi_drdy,

        QSPI_CSN_1V2             => QSPI_CSN_1V2,
        QSPI_D0                  => QSPI_D0,
        QSPI_D1                  => QSPI_D1,
        QSPI_D2                  => QSPI_D2,
        QSPI_D3                  => QSPI_D3,
        QSPI_CLK                 => QSPI_CLK,
        SPI_INGRESS_SCLK         => SPI_INGRESS_SCLK,
        SPI_INGRESS_CSN          => SPI_INGRESS_CSN,
        SPI_INGRESS_MISO         => SPI_INGRESS_MISO,
        SPI_INGRESS_MOSI         => SPI_INGRESS_MOSI,
        SPI_EGRESS_MOSI          => SPI_EGRESS_MOSI,
        SPI_EGRESS_CSN           => SPI_EGRESS_CSN,
        SPI_EGRESS_SCLK          => SPI_EGRESS_SCLK,
        SPI_EGRESS_MISO          => SPI_EGRESS_MISO,
        MAX_FPGA_HB_1V2          => MAX_FPGA_HB_1V2,
        FPGA_MAX_HB              => FPGA_MAX_HB,
        FPGA_MAX_FPGA_SEU_1V2    => FPGA_MAX_FPGA_SEU_1V2,
        FPGA_MAX_THRM_SHTD_N_1V2 => FPGA_MAX_THRM_SHTD_N_1V2
    );

    -- HBM
    hbm_top_g: if HBM_MODULES /= 0 generate
        hbm_top_i: entity work.HBM_FB2CDG1
        generic map(
            HBM_PORTS           => HBM_PORTS_PER_MODULE,
            HBM_AXI_ID_WIDTH    => HBM_AXI_ID_WIDTH,
            HBM_AXI_ADDR_WIDTH  => HBM_AXI_ADDR_WIDTH,
            HBM_AXI_LEN_WIDTH   => HBM_AXI_LEN_WIDTH,
            HBM_AXI_SIZE_WIDTH  => HBM_AXI_SIZE_WIDTH,
            HBM_AXI_BURST_WIDTH => HBM_AXI_BURST_WIDTH,
            HBM_AXI_DATA_WIDTH  => HBM_AXI_DATA_WIDTH,
            HBM_AXI_RESP_WIDTH  => HBM_AXI_RESP_WIDTH
        ) port map(
            CORE_PLL_REFCLK_CLK             => CLK_UIB1_FBR1_P,
            HBM_CATTRIP_VIRTUAL_I_CONDUIT   => HBM_TOP_CATTRIP_VIRTUAL,
            HBM_TEMP_VIRTUAL_I_CONDUIT      => HBM_TOP_TEMP_VIRTUAL,
            UIBPLL_REFCLK_CLK               => CLK_UIB1_P,
            HBM_ONLY_RESET_RESET            => not FPGA_RESETN_1V2,
            NOC_CLK_CTRL_REFCLK_CLK         => CLK_NOC_TOP,

            HBM_CLK         => hbm_clk(HBM_TOP_R),
            HBM_RST         => hbm_rst(HBM_TOP_R),
            HBM_INIT_DONE   => hbm_init_done(HBM_TOP_R),

            HBM_AXI_AWID    => hbm_axi_awid(HBM_TOP_R),
            HBM_AXI_AWADDR  => hbm_axi_awaddr(HBM_TOP_R),
            HBM_AXI_AWLEN   => hbm_axi_awlen(HBM_TOP_R),
            HBM_AXI_AWSIZE  => hbm_axi_awsize(HBM_TOP_R),
            HBM_AXI_AWBURST => hbm_axi_awburst(HBM_TOP_R),
            HBM_AXI_AWVALID => hbm_axi_awvalid(HBM_TOP_R),
            HBM_AXI_AWREADY => hbm_axi_awready(HBM_TOP_R),

            HBM_AXI_WDATA   => hbm_axi_wdata(HBM_TOP_R),
            HBM_AXI_WSTRB   => hbm_axi_wstrb(HBM_TOP_R),
            HBM_AXI_WLAST   => hbm_axi_wlast(HBM_TOP_R),
            HBM_AXI_WVALID  => hbm_axi_wvalid(HBM_TOP_R),
            HBM_AXI_WREADY  => hbm_axi_wready(HBM_TOP_R),

            HBM_AXI_BID     => hbm_axi_bid(HBM_TOP_R),
            HBM_AXI_BRESP   => hbm_axi_bresp(HBM_TOP_R),
            HBM_AXI_BVALID  => hbm_axi_bvalid(HBM_TOP_R),
            HBM_AXI_BREADY  => hbm_axi_bready(HBM_TOP_R),

            HBM_AXI_ARID    => hbm_axi_arid(HBM_TOP_R),
            HBM_AXI_ARADDR  => hbm_axi_araddr(HBM_TOP_R),
            HBM_AXI_ARLEN   => hbm_axi_arlen(HBM_TOP_R),
            HBM_AXI_ARSIZE  => hbm_axi_arsize(HBM_TOP_R),
            HBM_AXI_ARBURST => hbm_axi_arburst(HBM_TOP_R),
            HBM_AXI_ARVALID => hbm_axi_arvalid(HBM_TOP_R),
            HBM_AXI_ARREADY => hbm_axi_arready(HBM_TOP_R),

            HBM_AXI_RID     => hbm_axi_rid(HBM_TOP_R),
            HBM_AXI_RDATA   => hbm_axi_rdata(HBM_TOP_R),
            HBM_AXI_RRESP   => hbm_axi_rresp(HBM_TOP_R),
            HBM_AXI_RLAST   => hbm_axi_rlast(HBM_TOP_R),
            HBM_AXI_RVALID  => hbm_axi_rvalid(HBM_TOP_R),
            HBM_AXI_RREADY  => hbm_axi_rready(HBM_TOP_R)
        );
    end generate;

    hbm_bottom_g: if HBM_MODULES = 2 generate
        hbm_bottom_i: entity work.HBM_FB2CDG1
        generic map(
            HBM_PORTS           => HBM_PORTS_PER_MODULE,
            HBM_AXI_ID_WIDTH    => HBM_AXI_ID_WIDTH,
            HBM_AXI_ADDR_WIDTH  => HBM_AXI_ADDR_WIDTH,
            HBM_AXI_LEN_WIDTH   => HBM_AXI_LEN_WIDTH,
            HBM_AXI_SIZE_WIDTH  => HBM_AXI_SIZE_WIDTH,
            HBM_AXI_BURST_WIDTH => HBM_AXI_BURST_WIDTH,
            HBM_AXI_DATA_WIDTH  => HBM_AXI_DATA_WIDTH,
            HBM_AXI_RESP_WIDTH  => HBM_AXI_RESP_WIDTH
        ) port map(
            CORE_PLL_REFCLK_CLK             => CLK_UIB0_FBR0_P,
            HBM_CATTRIP_VIRTUAL_I_CONDUIT   => HBM_BOT_CATTRIP_VIRTUAL,
            HBM_TEMP_VIRTUAL_I_CONDUIT      => HBM_BOT_TEMP_VIRTUAL,
            UIBPLL_REFCLK_CLK               => CLK_UIB0_P,
            HBM_ONLY_RESET_RESET            => not FPGA_RESETN_1V2,
            NOC_CLK_CTRL_REFCLK_CLK         => CLK_NOC_BOTTOM,

            HBM_CLK         => hbm_clk(HBM_BOT_R),
            HBM_RST         => hbm_rst(HBM_BOT_R),
            HBM_INIT_DONE   => hbm_init_done(HBM_BOT_R),

            HBM_AXI_AWID    => hbm_axi_awid(HBM_BOT_R),
            HBM_AXI_AWADDR  => hbm_axi_awaddr(HBM_BOT_R),
            HBM_AXI_AWLEN   => hbm_axi_awlen(HBM_BOT_R),
            HBM_AXI_AWSIZE  => hbm_axi_awsize(HBM_BOT_R),
            HBM_AXI_AWBURST => hbm_axi_awburst(HBM_BOT_R),
            HBM_AXI_AWVALID => hbm_axi_awvalid(HBM_BOT_R),
            HBM_AXI_AWREADY => hbm_axi_awready(HBM_BOT_R),

            HBM_AXI_WDATA   => hbm_axi_wdata(HBM_BOT_R),
            HBM_AXI_WSTRB   => hbm_axi_wstrb(HBM_BOT_R),
            HBM_AXI_WLAST   => hbm_axi_wlast(HBM_BOT_R),
            HBM_AXI_WVALID  => hbm_axi_wvalid(HBM_BOT_R),
            HBM_AXI_WREADY  => hbm_axi_wready(HBM_BOT_R),

            HBM_AXI_BID     => hbm_axi_bid(HBM_BOT_R),
            HBM_AXI_BRESP   => hbm_axi_bresp(HBM_BOT_R),
            HBM_AXI_BVALID  => hbm_axi_bvalid(HBM_BOT_R),
            HBM_AXI_BREADY  => hbm_axi_bready(HBM_BOT_R),

            HBM_AXI_ARID    => hbm_axi_arid(HBM_BOT_R),
            HBM_AXI_ARADDR  => hbm_axi_araddr(HBM_BOT_R),
            HBM_AXI_ARLEN   => hbm_axi_arlen(HBM_BOT_R),
            HBM_AXI_ARSIZE  => hbm_axi_arsize(HBM_BOT_R),
            HBM_AXI_ARBURST => hbm_axi_arburst(HBM_BOT_R),
            HBM_AXI_ARVALID => hbm_axi_arvalid(HBM_BOT_R),
            HBM_AXI_ARREADY => hbm_axi_arready(HBM_BOT_R),

            HBM_AXI_RID     => hbm_axi_rid(HBM_BOT_R),
            HBM_AXI_RDATA   => hbm_axi_rdata(HBM_BOT_R),
            HBM_AXI_RRESP   => hbm_axi_rresp(HBM_BOT_R),
            HBM_AXI_RLAST   => hbm_axi_rlast(HBM_BOT_R),
            HBM_AXI_RVALID  => hbm_axi_rvalid(HBM_BOT_R),
            HBM_AXI_RREADY  => hbm_axi_rready(HBM_BOT_R)
        );
    end generate;

end architecture;
