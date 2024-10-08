-- fpga.vhd: PD-FALCON board top level entity and architecture
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author: Denis Kurka <xkurka05@stud.fit.vutbr.cz>
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
    -- FPGA system clock
    UFPGA_CLK100        : in    std_logic;

    -- PCIe0 Gen3 1x16
    PCIE0_SYSCLK0_P     : in std_logic;
    PCIE0_SYSRST_N      : in std_logic;
    PCIE0_RX_P          : in std_logic_vector(16-1 downto 0);
    PCIE0_TX_P          : out std_logic_vector(16-1 downto 0);

    -- QSFP
    -- =========================================================================
    REFCLK_R9A1         : in std_logic; -- 156.25 MHZ
    REFCLK_R9C1         : in std_logic; -- 156.25 MHZ
    REFCLK_R9A2         : in std_logic; -- 156.25 MHZ
    REFCLK_R9C2         : in std_logic; -- 156.25 MHZ

    QSFP1_RX_P          : in std_logic_vector(4-1 downto 0); 
    QSFP1_RX_N          : in std_logic_vector(4-1 downto 0);
    QSFP1_TX_P          : out std_logic_vector(4-1 downto 0);
    QSFP1_TX_N          : out std_logic_vector(4-1 downto 0);

    QSFP2_RX_P          : in std_logic_vector(4-1 downto 0); 
    QSFP2_RX_N          : in std_logic_vector(4-1 downto 0);
    QSFP2_TX_P          : out std_logic_vector(4-1 downto 0);
    QSFP2_TX_N          : out std_logic_vector(4-1 downto 0);

    QSFP3_RX_P          : in std_logic_vector(4-1 downto 0); 
    QSFP3_RX_N          : in std_logic_vector(4-1 downto 0);
    QSFP3_TX_P          : out std_logic_vector(4-1 downto 0);
    QSFP3_TX_N          : out std_logic_vector(4-1 downto 0);

    QSFP4_RX_P          : in std_logic_vector(4-1 downto 0); 
    QSFP4_RX_N          : in std_logic_vector(4-1 downto 0);
    QSFP4_TX_P          : out std_logic_vector(4-1 downto 0);
    QSFP4_TX_N          : out std_logic_vector(4-1 downto 0);

    -- Status LEDs
    LED_USR_R_RGY1      : out std_logic;
    LED_USR_Y_RGY1      : out std_logic;
    LED_USR_G_RGY1      : out std_logic;
    LED_USR_R_RGY2      : out std_logic;
    LED_USR_Y_RGY2      : out std_logic;
    LED_USR_G_RGY2      : out std_logic
);
end entity;

architecture FULL of FPGA is

    constant PCIE_LANES     : integer := 16;
    constant PCIE_CLKS      : integer := 1;
    constant PCIE_CONS      : integer := 1;
    constant MISC_IN_WIDTH  : integer := 8;
    constant MISC_OUT_WIDTH : integer := 8;
    constant ETH_LANES      : integer := 4;
    constant DMA_MODULES    : integer := ETH_PORTS;
    constant DMA_ENDPOINTS  : integer := tsel(PCIE_ENDPOINT_MODE=1,PCIE_ENDPOINTS,4*PCIE_ENDPOINTS);
    constant STATUS_LEDS    : natural := 2; -- fake leds

    constant MEM_PORTS          : integer := 0;
    constant MEM_ADDR_WIDTH     : integer := 27;
    constant MEM_DATA_WIDTH     : integer := 512;
    constant MEM_BURST_WIDTH    : integer := 7;

begin

    cm_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 10.0,
        PLL_MULT_F              => 12.0,
        PLL_MASTER_DIV          => 1,
        PLL_OUT0_DIV_F          => 3.0,
        PLL_OUT1_DIV            => 4,
        PLL_OUT2_DIV            => 6,
        PLL_OUT3_DIV            => 12,

        USE_PCIE_CLK            => FALSE,

        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,
        PCIE_CONS               => PCIE_CONS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => ETH_PORTS,
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => ETH_PORTS,

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

        MEM_PORTS               => MEM_PORTS,
        MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH,
        MEM_DATA_WIDTH          => MEM_DATA_WIDTH,
        MEM_BURST_WIDTH         => MEM_BURST_WIDTH,
        AMM_FREQ_KHZ            => 266660,

        BOARD                   => CARD_NAME,
        DEVICE                  => "STRATIX10"
    )
    port map(
        SYSCLK                  => UFPGA_CLK100,
        SYSRST                  => '0',

        PCIE_SYSCLK_P(0)        => PCIE0_SYSCLK0_P,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N(0)        => PCIE0_SYSRST_N,

        PCIE_RX_P               => PCIE0_RX_P,
        PCIE_RX_N               => (others => '0'),

        PCIE_TX_P               => PCIE0_TX_P,
        PCIE_TX_N               => open,

        ETH_REFCLK_P            => REFCLK_R9C1 & REFCLK_R9C2 & REFCLK_R9A1 & REFCLK_R9A2, --REFCLK_R9A1 & REFCLK_R9C1 & REFCLK_R9A1 & REFCLK_R9C1, -- & REFCLK_R9C1 & REFCLK_R9C1,
        ETH_REFCLK_N            => (others => '0'),

        ETH_RX_P(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_RX_P(4-1 downto 0),
        ETH_RX_P(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_RX_P(4-1 downto 0),
        ETH_RX_P(3*ETH_LANES-1 downto 2*ETH_LANES) => QSFP3_RX_P(4-1 downto 0),
        ETH_RX_P(4*ETH_LANES-1 downto 3*ETH_LANES) => QSFP4_RX_P(4-1 downto 0),

        ETH_RX_N(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_RX_N(4-1 downto 0),
        ETH_RX_N(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_RX_N(4-1 downto 0),
        ETH_RX_N(3*ETH_LANES-1 downto 2*ETH_LANES) => QSFP3_RX_N(4-1 downto 0),
        ETH_RX_N(4*ETH_LANES-1 downto 3*ETH_LANES) => QSFP4_RX_N(4-1 downto 0),

        ETH_TX_P(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_TX_P(4-1 downto 0),
        ETH_TX_P(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_TX_P(4-1 downto 0),
        ETH_TX_P(3*ETH_LANES-1 downto 2*ETH_LANES) => QSFP3_TX_P(4-1 downto 0),
        ETH_TX_P(4*ETH_LANES-1 downto 3*ETH_LANES) => QSFP4_TX_P(4-1 downto 0),

        ETH_TX_N(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_TX_N(4-1 downto 0),
        ETH_TX_N(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_TX_N(4-1 downto 0),
        ETH_TX_N(3*ETH_LANES-1 downto 2*ETH_LANES) => QSFP3_TX_N(4-1 downto 0),
        ETH_TX_N(4*ETH_LANES-1 downto 3*ETH_LANES) => QSFP4_TX_N(4-1 downto 0),

        ETH_LED_R               => open,
        ETH_LED_G               => open,

        QSFP_I2C_SCL(0)         => open,
        QSFP_I2C_SDA(0)         => open,

        QSFP_MODSEL_N           => open,
        QSFP_LPMODE             => open,
        QSFP_RESET_N            => open,
        QSFP_MODPRS_N           => (others => '0'),
        QSFP_INT_N              => (others => '0'),

        MEM_CLK                 => (others => '0'),
        MEM_RST                 => (others => '0'),

        MEM_AVMM_READY          => (others => '0'),
        MEM_AVMM_READ           => open,
        MEM_AVMM_WRITE          => open,
        MEM_AVMM_ADDRESS        => open,
        MEM_AVMM_BURSTCOUNT     => open,
        MEM_AVMM_WRITEDATA      => open,
        MEM_AVMM_READDATA       => (others => (others => '0')),
        MEM_AVMM_READDATAVALID  => (others => '0'),

        EMIF_RST_REQ            => open,
        EMIF_RST_DONE           => (others => '0'),
        EMIF_ECC_USR_INT        => (others => '0'),
        EMIF_CAL_SUCCESS        => (others => '0'),
        EMIF_CAL_FAIL           => (others => '0'),

        STATUS_LED_G(0)         => LED_USR_G_RGY1,
        STATUS_LED_G(1)         => LED_USR_G_RGY2,
        STATUS_LED_R(0)         => LED_USR_R_RGY1,
        STATUS_LED_R(1)         => LED_USR_R_RGY2,

        MISC_IN                 => (others => '0'),
        MISC_OUT                => open
    );

end architecture;
