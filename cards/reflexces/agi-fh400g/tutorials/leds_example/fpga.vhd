-- fpga.vhd: XpressSX AGI-FH400G card top-level entity and architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity FPGA is
port (
    -- =========================================================================
    --  GENERAL INTERFACES
    -- =========================================================================
    -- HW ID pins
    HW_ID            : in    std_logic_vector(3 downto 0);
    -- User LEDs
    AG_LED_G         : out   std_logic_vector(1 downto 0);
    AG_LED_R         : out   std_logic_vector(1 downto 0);
    -- I2C interface (access to I2C peripherals from FPGA)
    AG_I2C_SCLK      : inout std_logic;
    AG_I2C_SDA       : inout std_logic;

    -- =========================================================================
    --  GENERAL CLOCKS AND PLL STATUS SIGNALS
    -- =========================================================================
    -- External differential clocks (programmable via Ext. PLL)
    AG_SYSCLK0_P     : in    std_logic; -- 125 MHz
    AG_SYSCLK1_P     : in    std_logic; -- 100 MHz
    -- External PLL status
    AG_CLK_INT_N     : in    std_logic; -- indicates a change of LOL
    AG_CLK_GEN_LOL_N : in    std_logic; -- Loss Of Lock
    -- External 1PPS clock input
    AG_EXT_SYNC_1HZ  : in    std_logic;

    -- =========================================================================
    --  GENERAL RESETS - DANGEROUS!
    -- =========================================================================
    AG_DEV_POR_N     : in    std_logic; -- Card Power on Reset status
    AG_RST_N         : in    std_logic; -- Card Reset status
    AG_SOFT_RST      : out   std_logic; -- Card Soft Reset request
    AG_M10_RST_N     : out   std_logic; -- MAX10 Reset request

    -- =========================================================================
    --  MAX10 CONFIGURATION INTERFACE - DANGEROUS!
    -- =========================================================================
    -- Agilex can controlled MAX10 booting or reconfiguration:
    AG_M10_IMG_SEL_N : out   std_logic; -- MAX10 image selection
    AG_M10_REBOOT_N  : out   std_logic; -- MAX10 reboot request
    M10_AG_STATUS_N  : in    std_logic; -- MAX10 status
    M10_AG_DONE      : in    std_logic; -- MAX10 configuration done
        
    -- =========================================================================
    --  AGILEX CONFIGURATION REUEST INTERFACE
    -- =========================================================================
    -- Agilex can requested FPGA reboot via MAX10
    AG_CFG_IMG_SEL   : out   std_logic;	-- Agilex image selection
    AG_REQ_CONF_N    : out   std_logic; -- Agilex configuration reuest

    -- =========================================================================
    --  FLASH INTERFACE (disable for now, QSPI flash used by default)
    -- =========================================================================
    --FLASH_A                 : out   std_logic_vector(26 downto 0); -- Memory Address bus
    --FLASH_D                 : inout std_logic_vector(15 downto 0); -- Memory Data bus
    FLASH_CE0_N             : out   std_logic;                     -- Memory 0 Chip Enable (active is LOW)
    FLASH_CE1_N             : out   std_logic                      -- Memory 0 Chip Enable (active is LOW)
    --FLASH_OE_N              : out   std_logic;                     -- Memory Output Enable (both, active is LOW)
    --FLASH_WE_N              : out   std_logic;                     -- Memory Write Enable (both, active is LOW)
    --FLASH_RY_BY_N           : in    std_logic;                     -- Memory Ready/busy signal (both)
    --FLASH_BYTE_N            : out   std_logic;                     -- Memory data bus width (8bits for both, active is LOW)
    --FLASH_WP_N              : out   std_logic;                     -- Memory data Write protect signal (for both, active is LOW)
    --FLASH_RST_N             : out   std_logic;                     -- Memory reset signal (for both, active is LOW)     

    -- =========================================================================
    --  PCIE INTERFACES
    -- =========================================================================
    -- PCIe global
    ---- External PCIe clock selection: 1 = PCIe is slave,
    ----                                0 = PCIe is master
    --PCIE1_CLK_SEL_N         : out   std_logic;
    --PCIE2_CLK_SEL_N         : out   std_logic;
    ---- PCIe0 (Edge Connector)
    --PCIE0_CLK0_P            : in    std_logic;
    --PCIE0_CLK1_P            : in    std_logic;
    --PCIE0_PERST_N           : in    std_logic;
    --PCIE0_RX_P              : in    std_logic_vector(15 downto 0);
    --PCIE0_RX_N              : in    std_logic_vector(15 downto 0);
    --PCIE0_TX_P              : out   std_logic_vector(15 downto 0);
    --PCIE0_TX_N              : out   std_logic_vector(15 downto 0);
    ---- PCIe1 (External Connector: EXT0, J1201 and J1202 in schematics)
    --PCIE1_CLK0_P            : in    std_logic;
    --PCIE1_CLK1_P            : in    std_logic;
    --PCIE1_PERST_N           : in    std_logic;
    --PCIE1_RX_P              : in    std_logic_vector(15 downto 0);
    --PCIE1_RX_N              : in    std_logic_vector(15 downto 0);
    --PCIE1_TX_P              : out   std_logic_vector(15 downto 0);
    --PCIE1_TX_N              : out   std_logic_vector(15 downto 0);
    ---- PCIe2 (External Connector: EXT1, J1203 and J1204 in schematics)
    --PCIE2_CLK0_P            : in    std_logic;
    --PCIE2_CLK1_P            : in    std_logic;
    --PCIE2_PERST_N           : in    std_logic;
    --PCIE2_RX_P              : in    std_logic_vector(15 downto 0);
    --PCIE2_RX_N              : in    std_logic_vector(15 downto 0);
    --PCIE2_TX_P              : out   std_logic_vector(15 downto 0);
    --PCIE2_TX_N              : out   std_logic_vector(15 downto 0);

    -- =========================================================================
    --  QSFP-DD INTERFACES - F-TILE
    -- =========================================================================
    -- QSFP control
    --QSFP_I2C_SCL            : inout std_logic;
    --QSFP_I2C_SDA            : inout std_logic;
    --QSFP_MODSEL_N           : out   std_logic;
    --QSFP_INITMODE           : out   std_logic; -- LPmode
    --QSFP_RST_N              : out   std_logic;
    --QSFP_MODPRS_N           : in    std_logic;
    --QSFP_INT_N              : in    std_logic;
    --QSFP_REFCLK0_P          : in    std_logic;
    --QSFP_REFCLK0_N          : in    std_logic;
    --QSFP_REFCLK1_P          : in    std_logic;
    --QSFP_REFCLK1_N          : in    std_logic;
    --QSFP_RX_P               : in    std_logic_vector(7 downto 0);
    --QSFP_RX_N               : in    std_logic_vector(7 downto 0);
    --QSFP_TX_P               : out   std_logic_vector(7 downto 0);
    --QSFP_TX_N               : out   std_logic_vector(7 downto 0);
    --QSFP_LED_G              : out   std_logic_vector(7 downto 0);
    --QSFP_LED_R              : out   std_logic_vector(7 downto 0);

    -- =========================================================================
    --  SODIMM INTERFACES
    -- =========================================================================
    -- SODIMM0 port
    --SODIMM0_REFCLK_P : in    std_logic; -- 33.333 MHz
    --SODIMM0_OCT_RZQ  : in    std_logic;
    --SODIMM0_PCK      : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_NCK      : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_A        : out   std_logic_vector(17-1 downto 0);
    --SODIMM0_NACT     : out   std_logic;
    --SODIMM0_BA       : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_BG       : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_CKE      : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_NCS      : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_ODT      : out   std_logic_vector(2-1 downto 0);
    --SODIMM0_NRST     : out   std_logic;
    --SODIMM0_PAR      : out   std_logic;
    --SODIMM0_NALERT   : in    std_logic;
    --SODIMM0_PDQS     : inout std_logic_vector(9-1 downto 0);
    --SODIMM0_NDQS     : inout std_logic_vector(9-1 downto 0);
    --SODIMM0_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    --SODIMM0_DQ       : inout std_logic_vector(64-1 downto 0);
    --SODIMM0_CHKB     : inout std_logic_vector(8-1 downto 0);
    -- SODIMM1 port
    --SODIMM1_REFCLK_P : in    std_logic; -- 33.333 MHz
    --SODIMM1_OCT_RZQ  : in    std_logic;
    --SODIMM1_PCK      : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_NCK      : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_A        : out   std_logic_vector(17-1 downto 0);
    --SODIMM1_NACT     : out   std_logic;
    --SODIMM1_BA       : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_BG       : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_CKE      : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_NCS      : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_ODT      : out   std_logic_vector(2-1 downto 0);
    --SODIMM1_NRST     : out   std_logic;
    --SODIMM1_PAR      : out   std_logic;
    --SODIMM1_NALERT   : in    std_logic;
    --SODIMM1_PDQS     : inout std_logic_vector(9-1 downto 0);
    --SODIMM1_NDQS     : inout std_logic_vector(9-1 downto 0);
    --SODIMM1_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    --SODIMM1_DQ       : inout std_logic_vector(64-1 downto 0);
    --SODIMM1_CHKB     : inout std_logic_vector(8-1 downto 0);

    -- =========================================================================
    --  HPS (HARD PROCESSOR SYSTEM) INTERFACES (disable in first version)
    -- =========================================================================
    --HPS_CLK_100MHZ   : in    std_logic;
    ---- SD Card interface
    --HPS_MMC_CLK      : out   std_logic;
    --HPS_MMC_CMD      : inout std_logic;
    --HPS_MMC_DATA     : inout std_logic_vector(3 downto 0);
    ---- USB interface
    --HPS_USB_CLK      : in    std_logic;
    --HPS_USB_STP      : out   std_logic;
    --HPS_USB_DIR      : in    std_logic;
    --HPS_USB_NXT      : in    std_logic;
    --HPS_USB_DATA     : inout std_logic_vector(7 downto 0);
    ---- UART interface
    --HPS_UART_CTS     : in    std_logic;
    --HPS_UART_RTS     : out   std_logic;
    --HPS_UART_TXD     : out   std_logic;
    --HPS_UART_RXD     : in    std_logic;
    ---- I2C interface (access to I2C peripherals from HPS)
    --HPS_I2C1_SDA     : inout std_logic;
    --HPS_I2C1_SCL     : inout std_logic;
    ---- SPI interface (master) connected to MAX10
    --HPS_M10_SPI_MOSI : out   std_logic;
    --HPS_M10_SPI_MISO : in    std_logic;
    --HPS_M10_SPI_SS_N : out   std_logic;
    --HPS_M10_SPI_SCK  : out   std_logic;
    ---- General interface between HPS and MAX10
    --HPS_M10_RST_N    : inout std_logic; -- HPS reset request from MAX10
    --HPS_M10_INT_N    : inout std_logic; -- HPS interrupt request from MAX10
    --HPS_M10_ACK      : inout std_logic; -- Optional acknowledgment of an operation

    -- =========================================================================
    --  ONBOARD DDR4 INTERFACE (designed for HPS)
    -- =========================================================================
    --HPS_DDR4_REFCLK_P : in    std_logic; -- 33.333 MHz
    --HPS_DDR4_OCT_RZQ  : in    std_logic;
    --HPS_DDR4_DQ       : inout std_logic_vector(64-1 downto 0);
    --HPS_DDR4_DQS      : inout std_logic_vector(8-1 downto 0);
    --HPS_DDR4_DQS_N    : inout std_logic_vector(8-1 downto 0);
    --HPS_DDR4_DBI_N    : inout std_logic_vector(8-1 downto 0);
    --HPS_DDR4_BA       : out   std_logic_vector(2-1 downto 0);
    --HPS_DDR4_BG       : out   std_logic_vector(1-1 downto 0);
    --HPS_DDR4_ADDR     : out   std_logic_vector(17-1 downto 0);
    --HPS_DDR4_ALERT_N  : in    std_logic;
    --HPS_DDR4_RST_N    : out   std_logic;
    --HPS_DDR4_CS_N     : out   std_logic;
    --HPS_DDR4_ACT_N    : out   std_logic;
    --HPS_DDR4_ODT_N    : out   std_logic;
    --HPS_DDR4_CKE      : out   std_logic;
    --HPS_DDR4_CK       : out   std_logic;
    --HPS_DDR4_CK_N     : out   std_logic;
    --HPS_DDR4_PAR      : out   std_logic
);
end entity;

architecture FULL of FPGA is

    component reset_release is
    port (
        ninit_done : out std_logic   -- ninit_done
    );
    end component reset_release;

    component iopll0 is
    port (
        rst      : in  std_logic := 'X'; -- reset
        refclk   : in  std_logic := 'X'; -- clk
        locked   : out std_logic;        -- export
        outclk_0 : out std_logic         -- clk
    );
    end component iopll0;

    component iopll1 is
    port (
        rst      : in  std_logic := 'X'; -- reset
        refclk   : in  std_logic := 'X'; -- clk
        locked   : out std_logic;        -- export
        outclk_0 : out std_logic         -- clk
    );
    end component iopll1;

    constant COUNTER_W : natural := 28;

    signal ninit_done        : std_logic;
    signal pll0_locked       : std_logic;
    signal pll1_locked       : std_logic;
    signal pll0_clk_100m     : std_logic;
    signal pll1_clk_100m     : std_logic;
    signal pll0_clk_100m_rst : std_logic;
    signal pll1_clk_100m_rst : std_logic;
    signal counter0          : unsigned(COUNTER_W-1 downto 0);
    signal counter1          : unsigned(COUNTER_W-1 downto 0);

begin

    -- Disable access to flash memory
    FLASH_CE0_N <= '1';
    FLASH_CE1_N <= '1';

    AG_I2C_SCLK	<= 'Z';
    AG_I2C_SDA	<= 'Z';
    
    AG_SOFT_RST  <= '0';
    AG_M10_RST_N <= '1';

    AG_M10_IMG_SEL_N <= '1';
	 -- Must not be permanently assigned to GND!
    AG_M10_REBOOT_N  <= '1';

    AG_CFG_IMG_SEL <= '0';
    AG_REQ_CONF_N  <= '1';

    reset_release_i : component reset_release
    port map (
        ninit_done => ninit_done
    );

    pll0_i : component iopll0
    port map (
        rst      => ninit_done,
        refclk   => AG_SYSCLK0_P, -- 125 MHz
        locked   => pll0_locked,
        outclk_0 => pll0_clk_100m -- 100 MHz
    );

    pll1_i : component iopll1
    port map (
        rst      => ninit_done,
        refclk   => AG_SYSCLK1_P, -- 100 MHz
        locked   => pll1_locked,
        outclk_0 => pll1_clk_100m -- 100 MHz
    );

    rst0_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => pll0_clk_100m,
        ASYNC_RST  => not pll0_locked,
        OUT_RST(0) => pll0_clk_100m_rst
    );

    rst1_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => pll1_clk_100m,
        ASYNC_RST  => not pll1_locked,
        OUT_RST(0) => pll1_clk_100m_rst
    );

    process (pll0_clk_100m)
    begin
        if rising_edge(pll0_clk_100m) then
            if (pll0_clk_100m_rst = '1') then
                counter0 <= (others => '0');
                AG_LED_G <= (others => '0');
            else
                counter0 <= counter0 + 1;
                AG_LED_G <= std_logic_vector(counter1(COUNTER_W-1 downto COUNTER_W-2));
            end if;
        end if;
    end process;

    process (pll1_clk_100m)
    begin
        if rising_edge(pll1_clk_100m) then
            if (pll1_clk_100m_rst = '1') then
                counter1 <= (others => '0');
                AG_LED_R <= (others => '0');
            else
                counter1 <= counter1 + 1;
                AG_LED_R <= std_logic_vector(counter1(COUNTER_W-1 downto COUNTER_W-2));
            end if;
        end if;
    end process;

end architecture;
