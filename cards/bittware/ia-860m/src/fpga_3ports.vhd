-- fpga_2ports.vhd: Bittware IA-860m card top-level entity and architecture for 3 QSFP-DD port variant
-- Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
-- Author(s): Denis Kurka <kurka@dyna-nic.com>
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
    --  GENERAL CLOCKS AND PLL STATUS SIGNALS
    -- =========================================================================
    -- 100 MHz
    SYSCLK_100_P     : in    std_logic;

    -- =========================================================================
    --  PCIE INTERFACES
    -- =========================================================================
    PERST_L            : in     std_logic;
    PCIE_REFCLK0       : in     std_logic;
    PCIE_REFCLK1       : in     std_logic;
    PCIE_RX_P          : in     std_logic_vector(15 downto 0);
    PCIE_RX_N          : in     std_logic_vector(15 downto 0);
    PCIE_TX_P          : out    std_logic_vector(15 downto 0);
    PCIE_TX_N          : out    std_logic_vector(15 downto 0);

    -- =========================================================================
    -- F-Tile Clocking, used for the QSFP-DDs, MCIO and M.2 SSD
    -- =========================================================================
    -- Recovered Clocks (output from F-Tile)
    -- RECV0_CLK          : out    std_logic;  -- F-Tile 12A, Refclk #9
    -- RECV1_CLK          : out    std_logic;  -- F-Tile 13A, Refclk #9
    -- RECV2_CLK          : out    std_logic;  -- F-Tile 13C, Refclk #9

    -- =========================================================================
    --  QSFP-DD INTERFACES - F-TILE
    -- =========================================================================
    -----------------------------------------------------------------------------
    -- QSFPDD0
    -----------------------------------------------------------------------------
    QSFP0_REFCLK       : in     std_logic;  -- F-Tile 12A, Refclk #5
    QSFP0_TX_P         : out    std_logic_vector(7 downto 0);
    QSFP0_TX_N         : out    std_logic_vector(7 downto 0);
    QSFP0_RX_P         : in     std_logic_vector(7 downto 0);
    QSFP0_RX_N         : in     std_logic_vector(7 downto 0);
    -----------------------------------------------------------------------------
    -- QSFPDD1
    -----------------------------------------------------------------------------
    QSFP1_REFCLK       : in     std_logic;  -- F-Tile 13A, Refclk #5
    QSFP1_TX_P         : out    std_logic_vector(7 downto 0);
    QSFP1_TX_N         : out    std_logic_vector(7 downto 0);
    QSFP1_RX_P         : in     std_logic_vector(7 downto 0);
    QSFP1_RX_N         : in     std_logic_vector(7 downto 0);
    -----------------------------------------------------------------------------
    -- QSFPDD2
    -----------------------------------------------------------------------------
    QSFP2_REFCLK       : in     std_logic;  -- F-Tile 13C, Refclk #5
    QSFP2_TX_P         : out    std_logic_vector(7 downto 0);
    QSFP2_TX_N         : out    std_logic_vector(7 downto 0);
    QSFP2_RX_P         : in     std_logic_vector(7 downto 0);
    QSFP2_RX_N         : in     std_logic_vector(7 downto 0);

    -- =========================================================================
    -- BMC
    -- =========================================================================
    BMC_IF_PRESENT_L   : out    std_logic;

    FPGA_IG_SPI_SCK    : in     std_logic;
    FPGA_IG_SPI_PCS0   : in     std_logic;
    FPGA_IG_SPI_MOSI   : in     std_logic;
    FPGA_IG_SPI_MISO   : out    std_logic;
    FPGA_TO_BMC_IRQ    : out    std_logic;

    FPGA_EG_SPI_SCK    : out    std_logic;
    FPGA_EG_SPI_PCS0   : out    std_logic;
    FPGA_EG_SPI_MOSI   : out    std_logic;
    FPGA_EG_SPI_MISO   : in     std_logic;
    BMC_TO_FPGA_IRQ    : in     std_logic;

    -- Buffer Enables (both should be driven LOW)
    MCIO_GPIO_EN_L     : out    std_logic;
    EXT_GPIO_EN_L      : out    std_logic
);
end entity;

architecture FULL of FPGA is

    constant PCIE_LANES      : integer := 16;
    constant PCIE_CLKS       : integer := 2;
    constant PCIE_CONS       : integer := 1;
    constant MISC_IN_WIDTH   : integer := 64;
    constant MISC_OUT_WIDTH  : integer := 64 + 5;
    constant ETH_LANES       : integer := 8;
    constant DMA_ENDPOINTS   : integer := tsel(DMA_TYPE=3, 4, 1);
    constant QSFP_PORTS      : natural := 3;
    constant DEVICE          : string  := "AGILEX";

    --Ethernet
    signal eth_rx_p          : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_rx_n          : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_p          : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_n          : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    signal eth_refclk_p      : std_logic_vector(ETH_PORTS-1 downto 0);
    signal eth_refclk_n      : std_logic_vector(ETH_PORTS-1 downto 0);

    -- Boot
    signal bmc_mi_clk        : std_logic;
    signal bmc_mi_reset      : std_logic;
    signal bmc_mi_addr       : std_logic_vector(32-1 downto 0);
    signal bmc_mi_dwr        : std_logic_vector(32-1 downto 0);
    signal bmc_mi_be         : std_logic_vector(32/8-1 downto 0);
    signal bmc_mi_rd         : std_logic;
    signal bmc_mi_wr         : std_logic;
    signal bmc_mi_drd        : std_logic_vector(32-1 downto 0);
    signal bmc_mi_ardy       : std_logic;
    signal bmc_mi_drdy       : std_logic;

    signal qsfp_modprs_n    : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_int_n       : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_reset_n     : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_lpmode      : std_logic_vector(QSFP_PORTS-1 downto 0);

begin

    -- These signals must drive LOW when using the appropriate interfaces (MCIO and/or GPIO).
    -- Can be removed/ignored otherwise.
    MCIO_GPIO_EN_L <= '0';
    EXT_GPIO_EN_L  <= '0';

    -- QSFP MAPPING ------------------------------------------------------------
    eth_refclk_p <= QSFP2_REFCLK & QSFP1_REFCLK & QSFP0_REFCLK;
    eth_refclk_n <= (others => '0'); -- Quartus will handle the connection itself

    eth_rx_p <= QSFP2_RX_P & QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP2_RX_N & QSFP1_RX_N & QSFP0_RX_N;

    QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP2_TX_P <= eth_tx_p(3*ETH_LANES-1 downto 2*ETH_LANES);
    QSFP2_TX_N <= eth_tx_n(3*ETH_LANES-1 downto 2*ETH_LANES);

    cm_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 10.0,
        USE_PCIE_CLK            => false,

        PCIE_CONS               => PCIE_CONS,
        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => 1,
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => QSFP_PORTS,
        QSFP_I2C_PORTS          => QSFP_PORTS,
        QSFP_I2C_CTRL_EN        => false,

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

        PCIE_SYSCLK_P           => PCIE_REFCLK1 & PCIE_REFCLK0,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N           => (others => PERST_L),

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

        QSFP_MODPRS_N          => qsfp_modprs_n,
        QSFP_INT_N             => qsfp_int_n,
        QSFP_LPMODE            => qsfp_lpmode,
        QSFP_RESET_N           => qsfp_reset_n,

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

        BOOT_MI_CLK            => bmc_mi_clk,
        BOOT_MI_RESET          => bmc_mi_reset,
        BOOT_MI_DWR            => bmc_mi_dwr,
        BOOT_MI_ADDR           => bmc_mi_addr,
        BOOT_MI_RD             => bmc_mi_rd,
        BOOT_MI_WR             => bmc_mi_wr,
        BOOT_MI_BE             => bmc_mi_be,
        BOOT_MI_DRD            => bmc_mi_drd,
        BOOT_MI_ARDY           => bmc_mi_ardy,
        BOOT_MI_DRDY           => bmc_mi_drdy,

        MISC_IN                 => (others => '0'),
        MISC_OUT                => open
    );

    -- BMC controller
    bmc_wrap_i : entity work.BMC_WRAP
    generic map(
        DEVICE => DEVICE
    ) port map(
        CLK                     => bmc_mi_clk,
        RESET                   => bmc_mi_reset,

        MI_DWR                  => bmc_mi_dwr,
        MI_ADDR                 => bmc_mi_addr,
        MI_RD                   => bmc_mi_rd,
        MI_WR                   => bmc_mi_wr,
        MI_BE                   => bmc_mi_be,
        MI_DRD                  => bmc_mi_drd,
        MI_ARDY                 => bmc_mi_ardy,
        MI_DRDY                 => bmc_mi_drdy,

        QSFPDD0_RST_N           => qsfp_reset_n(0),
        QSFPDD0_LPMODE          => qsfp_lpmode(0),
        QSFPDD0_INT_N           => qsfp_int_n(0),
        QSFPDD0_PRESENT_N       => qsfp_modprs_n(0),

        QSFPDD1_RST_N           => qsfp_reset_n(1),
        QSFPDD1_LPMODE          => qsfp_lpmode(1),
        QSFPDD1_INT_N           => qsfp_int_n(1),
        QSFPDD1_PRESENT_N       => qsfp_modprs_n(1),

        QSFPDD2_RST_N           => qsfp_reset_n(2),
        QSFPDD2_LPMODE          => qsfp_lpmode(2),
        QSFPDD2_INT_N           => qsfp_int_n(2),
        QSFPDD2_PRESENT_N       => qsfp_modprs_n(2),

        BMC_IF_PRESENT_N        => BMC_IF_PRESENT_L,
        FPGA_IG_SPI_SCK         => FPGA_IG_SPI_SCK,
        FPGA_IG_SPI_PCS0        => FPGA_IG_SPI_PCS0,
        FPGA_IG_SPI_MOSI        => FPGA_IG_SPI_MOSI,
        FPGA_IG_SPI_MISO        => FPGA_IG_SPI_MISO,
        FPGA_TO_BMC_IRQ         => FPGA_TO_BMC_IRQ,
        FPGA_EG_SPI_SCK         => FPGA_EG_SPI_SCK,
        FPGA_EG_SPI_PCS0        => FPGA_EG_SPI_PCS0,
        FPGA_EG_SPI_MOSI        => FPGA_EG_SPI_MOSI,
        FPGA_EG_SPI_MISO        => FPGA_EG_SPI_MISO,
        BMC_TO_FPGA_IRQ         => BMC_TO_FPGA_IRQ
    );

end architecture;
