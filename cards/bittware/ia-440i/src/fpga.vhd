-- fpga.vhd: IA-440I board top level entity and architecture
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.combo_const.all;
use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;

entity FPGA is
port (
    -- FPGA system clock
    SYS_CLK_100M       : in    std_logic;
    -- User LEDs
    USER_LED_G         : out   std_logic;
    USER_LED_R         : out   std_logic;

    -- =========================================================================
    -- PCIe
    -- =========================================================================
    PCIE_REFCLK0       : in    std_logic;
    PCIE_REFCLK1       : in    std_logic;
    PCIE_SYSRST_N      : in    std_logic;
    PCIE_RX_P          : in    std_logic_vector(16-1 downto 0);
    PCIE_RX_N          : in    std_logic_vector(16-1 downto 0);
    PCIE_TX_P          : out   std_logic_vector(16-1 downto 0);
    PCIE_TX_N          : out   std_logic_vector(16-1 downto 0);

    -- =========================================================================
    -- QSFP
    -- =========================================================================
    QSFP_REFCLK_156M   : in    std_logic;
    QSFP_RX_P          : in    std_logic_vector(8-1 downto 0);
    QSFP_RX_N          : in    std_logic_vector(8-1 downto 0);
    QSFP_TX_P          : out   std_logic_vector(8-1 downto 0);
    QSFP_TX_N          : out   std_logic_vector(8-1 downto 0);

    -- =========================================================================
    -- BMC
    -- =========================================================================
    BMC_IF_PRESENT_N   : out   std_logic;
    BMC_RST_N          : in    std_logic;

    FPGA_EG_SPI_SCK    : out   std_logic;
    FPGA_EG_SPI_MISO   : in    std_logic;
    FPGA_EG_SPI_MOSI   : out   std_logic;
    FPGA_EG_SPI_PCS0   : out   std_logic;
    BMC_TO_FPGA_IRQ    : in    std_logic;

    FPGA_IG_SPI_SCK    : in    std_logic;
    FPGA_IG_SPI_MISO   : inout std_logic;
    FPGA_IG_SPI_MOSI   : in    std_logic;
    FPGA_IG_SPI_PCS0   : in    std_logic;
    FPGA_TO_BMC_IRQ    : out   std_logic

    -- BMC_GPIO0          : out   std_logic;
    -- BMC_GPIO1          : in    std_logic
);
end entity;

architecture FULL of FPGA is

    constant PCIE_LANES      : natural := 16;
    constant PCIE_CLKS       : natural := 2;
    constant PCIE_CONS       : natural := 1;
    constant MISC_IN_WIDTH   : natural := 4;
    constant MISC_OUT_WIDTH  : natural := 4;
    constant ETH_LANES       : natural := 8;
    constant DMA_ENDPOINTS   : natural := tsel(DMA_TYPE=3, 4, 1); -- 400G DMA Medusa = 4x DMA_ENDPOINT
    constant STATUS_LEDS     : natural := 2; -- fake, this board has only 1 status LED

    signal status_led_g      : std_logic_vector(STATUS_LEDS-1 downto 0);
    signal status_led_r      : std_logic_vector(STATUS_LEDS-1 downto 0);

    constant BMC_IF_PRESENT  : boolean := false;

    signal bmc_mi_clk        : std_logic;
    signal bmc_mi_reset      : std_logic;
    signal bmc_mi_dwr        : std_logic_vector(32-1 downto 0);
    signal bmc_mi_addr       : std_logic_vector(32-1 downto 0);
    signal bmc_mi_rd         : std_logic;
    signal bmc_mi_wr         : std_logic;
    signal bmc_mi_be         : std_logic_vector(4-1 downto 0);
    signal bmc_mi_drd        : std_logic_vector(32-1 downto 0);
    signal bmc_mi_ardy       : std_logic;
    signal bmc_mi_drdy       : std_logic;

begin

    cm_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 10.0,
        USE_PCIE_CLK            => false,

        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,
        PCIE_CONS               => PCIE_CONS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => 1, -- fake, this board has no ETH LEDs
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => 1,
        QSFP_I2C_PORTS          => 1,
        -- QSFP_I2C_TRISTATE       => ??,

        STATUS_LEDS             => STATUS_LEDS,
        MISC_IN_WIDTH           => MISC_IN_WIDTH,
        MISC_OUT_WIDTH          => MISC_OUT_WIDTH,

        PCIE_ENDPOINTS          => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE      => PCIE_MOD_ARCH,
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,

        DMA_ENDPOINTS           => DMA_ENDPOINTS,
        DMA_MODULES             => DMA_MODULES,

        DMA_RX_CHANNELS         => DMA_RX_CHANNELS/DMA_MODULES,
        DMA_TX_CHANNELS         => DMA_TX_CHANNELS/DMA_MODULES,

        BOARD                   => "IA-440I",
        DEVICE                  => "AGILEX"
    )
    port map(
        SYSCLK                 => SYS_CLK_100M,
        SYSRST                 => '0',

        PCIE_SYSCLK_P          => PCIE_REFCLK1 & PCIE_REFCLK0,
        PCIE_SYSCLK_N          => (others => '0'),
        PCIE_SYSRST_N(0)       => PCIE_SYSRST_N,
        PCIE_RX_P              => PCIE_RX_P,
        PCIE_RX_N              => PCIE_RX_N,
        PCIE_TX_P              => PCIE_TX_P,
        PCIE_TX_N              => PCIE_TX_N,

        ETH_REFCLK_P(0)        => QSFP_REFCLK_156M,
        ETH_REFCLK_N           => (others => '0'),
        ETH_RX_P               => QSFP_RX_P,
        ETH_RX_N               => QSFP_RX_N,
        ETH_TX_P               => QSFP_TX_P,
        ETH_TX_N               => QSFP_TX_N,

        -- QSFP_MODPRS_N          => ??,
        -- QSFP_INT_N             => ??,

        -- QSFP_I2C_SCL_I(0)      => qsfp_scl,
        -- QSFP_I2C_SDA_I(0)      => qsfp_sda,
        -- QSFP_I2C_SCL_O(0)      => qsfp_scl_o,
        -- QSFP_I2C_SCL_OE(0)     => qsfp_scl_oe,
        -- QSFP_I2C_SDA_O(0)      => qsfp_sda_o,
        -- QSFP_I2C_SDA_OE(0)     => qsfp_sda_oe,

        -- QSFP_MODSEL_N          => open,
        -- QSFP_LPMODE(0)         => ioexp_o(4),
        -- QSFP_RESET_N(0)        => ioexp_o(7),
        -- QSFP_MODPRS_N          => (others => ioexp_i(6)),
        -- QSFP_INT_N             => (others => ioexp_i(5)),

        STATUS_LED_G           => status_led_g,
        STATUS_LED_R           => status_led_r,

        MISC_IN                => (others => '0'),
        MISC_OUT               => open,

        BOOT_MI_CLK            => bmc_mi_clk,
        BOOT_MI_RESET          => bmc_mi_reset,
        BOOT_MI_DWR            => bmc_mi_dwr,
        BOOT_MI_ADDR           => bmc_mi_addr,
        BOOT_MI_RD             => bmc_mi_rd,
        BOOT_MI_WR             => bmc_mi_wr,
        BOOT_MI_BE             => bmc_mi_be,
        BOOT_MI_DRD            => bmc_mi_drd,
        BOOT_MI_ARDY           => bmc_mi_ardy,
        BOOT_MI_DRDY           => bmc_mi_drdy
    );

    USER_LED_G <= status_led_g(0);
    USER_LED_R <= status_led_r(0);

    bmc_if_open_g: if not BMC_IF_PRESENT generate
        BMC_IF_PRESENT_N <= '1';
    end generate;

    -- TODO: custom BMC boot controller
    -- boot_ctrl_i : entity work.BOOT_CTRL
    -- generic map (
    --     DEVICE    => DEVICE,
    --     BOOT_TYPE => 3
    -- )
    -- port map (
    --     MI_CLK        => boot_mi_clk,
    --     MI_RESET      => boot_mi_reset,
    --     MI_DWR        => boot_mi_dwr,
    --     MI_ADDR       => boot_mi_addr,
    --     MI_BE         => boot_mi_be,
    --     MI_RD         => boot_mi_rd,
    --     MI_WR         => boot_mi_wr,
    --     MI_ARDY       => boot_mi_ardy,
    --     MI_DRD        => boot_mi_drd,
    --     MI_DRDY       => boot_mi_drdy,
    -- ...

end architecture;
