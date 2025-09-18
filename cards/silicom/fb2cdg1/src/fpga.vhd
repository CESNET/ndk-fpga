-- fpga.vhd: Silicom ThunderFjord fb2cdg1 card top-level entity and architecture
-- Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.combo_const.all;
use work.combo_user_const.all;

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
    SYSCLK_100_P     : in    std_logic;

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
    FPGA_MAX_THRM_SHTD_N_1V2 : out    std_logic
);
end entity;

architecture FULL of FPGA is

    constant PCIE_LANES      : integer := 16;
    constant PCIE_CLKS       : integer := 2;
    constant PCIE_CONS       : integer := 1;
    constant MISC_IN_WIDTH   : integer := 64;
    constant MISC_OUT_WIDTH  : integer := 64 + 5;
    constant ETH_LANES       : integer := 8;
    constant DMA_ENDPOINTS   : integer := tsel(DMA_TYPE=3, 4, 1); -- 400G DMA Medusa = 4x DMA_ENDPOINT
    constant DEVICE          : string  := "AGILEX";

    --Ethernet
    signal eth_rx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_rx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    signal eth_refclk_p           : std_logic_vector(ETH_PORTS-1 downto 0);
    signal eth_refclk_n           : std_logic_vector(ETH_PORTS-1 downto 0);

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

    signal qspi_data_out          : std_logic_vector(4 - 1 downto 0);
    signal qspi_data_oe           : std_logic_vector(4 - 1 downto 0);

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

        PCIE_CONS               => PCIE_CONS,
        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
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
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,

        DMA_ENDPOINTS           => DMA_ENDPOINTS,
        DMA_MODULES             => DMA_MODULES,
        DMA_RX_CHANNELS         => DMA_RX_CHANNELS/DMA_MODULES,
        DMA_TX_CHANNELS         => DMA_TX_CHANNELS/DMA_MODULES
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

        --TODO: HBM

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
    QSPI_D0 <= qspi_data_out(0) when qspi_data_oe(0) = '1' else 'Z';
    QSPI_D1 <= qspi_data_out(1) when qspi_data_oe(1) = '1' else 'Z';
    QSPI_D2 <= qspi_data_out(2) when qspi_data_oe(2) = '1' else 'Z';
    QSPI_D3 <= qspi_data_out(3) when qspi_data_oe(3) = '1' else 'Z';

    pmci_i : entity work.PMCI_FB2CDG1
    generic map(
        DEVICE        => "AGILEX",
        G_SWB_RD_TYPE => 1 -- Thunderfjord
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

        FLASH_CTRLR_ATOM_PORTS_DCLK     => QSPI_CLK,
        FLASH_CTRLR_ATOM_PORTS_NCS      => QSPI_CSN_1V2,
        FLASH_CTRLR_ATOM_PORTS_OE       => open,
        FLASH_CTRLR_ATOM_PORTS_DATAOUT  => qspi_data_out,
        FLASH_CTRLR_ATOM_PORTS_DATAOE   => qspi_data_oe,
        FLASH_CTRLR_ATOM_PORTS_DATAIN   => QSPI_D3 & QSPI_D2 & QSPI_D1 & QSPI_D0,

        M10_GPIO_FPGA_USR_100M          => '0',
        M10_GPIO_FPGA_M10_HB            => MAX_FPGA_HB_1V2,
        M10_GPIO_PMCI_NIOS_HB           => FPGA_MAX_HB,
        M10_GPIO_M10_SEU_ERROR          => '0',
        M10_GPIO_FPGA_THERM_SHDN        => FPGA_MAX_THRM_SHTD_N_1V2,
        M10_GPIO_FPGA_SEU_ERROR         => FPGA_MAX_FPGA_SEU_1V2,

        SPI_INGRESS_SCLK                => SPI_INGRESS_SCLK,
        SPI_INGRESS_CSN                 => SPI_INGRESS_CSN,
        SPI_INGRESS_MISO                => SPI_INGRESS_MISO,
        SPI_INGRESS_MOSI                => SPI_INGRESS_MOSI,

        SPI_EGRESS_MOSI                 => SPI_EGRESS_MOSI,
        SPI_EGRESS_CSN                  => SPI_EGRESS_CSN,
        SPI_EGRESS_SCLK                 => SPI_EGRESS_SCLK,
        SPI_EGRESS_MISO                 => SPI_EGRESS_MISO
    );

end architecture;
