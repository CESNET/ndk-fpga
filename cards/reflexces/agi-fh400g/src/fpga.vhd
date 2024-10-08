-- fpga.vhd: XpressSX AGI-FH400G card top-level entity and architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
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
    FLASH_A                 : out   std_logic_vector(26 downto 0); -- Memory Address bus
    FLASH_D                 : inout std_logic_vector(15 downto 0); -- Memory Data bus
    FLASH_CE0_N             : out   std_logic;                     -- Memory 0 Chip Enable (active is LOW)
    FLASH_CE1_N             : out   std_logic;                     -- Memory 0 Chip Enable (active is LOW)
    FLASH_OE_N              : out   std_logic;                     -- Memory Output Enable (both, active is LOW)
    FLASH_WE_N              : out   std_logic;                     -- Memory Write Enable (both, active is LOW)
    --FLASH_RY_BY_N           : in    std_logic;                     -- Memory Ready/busy signal (both)
    --FLASH_BYTE_N            : out   std_logic;                     -- Memory data bus width (8bits for both, active is LOW)
    --FLASH_WP_N              : out   std_logic;                     -- Memory data Write protect signal (for both, active is LOW)
    --FLASH_RST_N             : out   std_logic;                     -- Memory reset signal (for both, active is LOW)     

    -- =========================================================================
    --  PCIE INTERFACES
    -- =========================================================================
    -- External PCIe clock selection: 1 = PCIe is slave,
    --                                0 = PCIe is master
    PCIE1_CLK_SEL_N         : out   std_logic;
    PCIE2_CLK_SEL_N         : out   std_logic;
    -- PCIe0 (Edge Connector)
    PCIE0_CLK0_P            : in    std_logic;
    PCIE0_CLK1_P            : in    std_logic;
    PCIE0_PERST_N           : in    std_logic;
    PCIE0_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE0_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE0_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE0_TX_N              : out   std_logic_vector(15 downto 0);
    -- PCIe1 (External Connector: EXT0, J1201 and J1202 in schematics)
    PCIE1_CLK0_P            : in    std_logic;
    PCIE1_CLK1_P            : in    std_logic;
    PCIE1_PERST_N           : in    std_logic;
    PCIE1_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE1_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE1_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE1_TX_N              : out   std_logic_vector(15 downto 0);
    -- PCIe2 (External Connector: EXT1, J1203 and J1204 in schematics)
    PCIE2_CLK0_P            : in    std_logic;
    PCIE2_CLK1_P            : in    std_logic;
    PCIE2_PERST_N           : in    std_logic;
    PCIE2_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE2_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE2_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE2_TX_N              : out   std_logic_vector(15 downto 0);

    -- =========================================================================
    --  QSFP-DD INTERFACES - F-TILE
    -- =========================================================================
    -- QSFP control
    QSFP_I2C_SCL            : inout std_logic;
    QSFP_I2C_SDA            : inout std_logic;
    QSFP_MODSEL_N           : out   std_logic;
    QSFP_INITMODE           : out   std_logic; -- LPmode
    QSFP_RST_N              : out   std_logic;
    QSFP_MODPRS_N           : in    std_logic;
    QSFP_INT_N              : in    std_logic;
    QSFP_REFCLK0_P          : in    std_logic;
    --QSFP_REFCLK0_N          : in    std_logic;
    --QSFP_REFCLK1_P          : in    std_logic;
    --QSFP_REFCLK1_N          : in    std_logic;
    QSFP_RX_P               : in    std_logic_vector(7 downto 0);
    QSFP_RX_N               : in    std_logic_vector(7 downto 0);
    QSFP_TX_P               : out   std_logic_vector(7 downto 0);
    QSFP_TX_N               : out   std_logic_vector(7 downto 0);
    QSFP_LED_G              : out   std_logic_vector(7 downto 0);
    QSFP_LED_R              : out   std_logic_vector(7 downto 0);

    -- =========================================================================
    --  SODIMM INTERFACES
    -- =========================================================================
    -- SODIMM0 port
    SODIMM0_REFCLK_P : in    std_logic; -- 33.333 MHz
    SODIMM0_OCT_RZQ  : in    std_logic;
    SODIMM0_PCK      : out   std_logic_vector(2-1 downto 0);
    SODIMM0_NCK      : out   std_logic_vector(2-1 downto 0);
    SODIMM0_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM0_NACT     : out   std_logic;
    SODIMM0_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM0_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM0_CKE      : out   std_logic_vector(2-1 downto 0);
    SODIMM0_NCS      : out   std_logic_vector(2-1 downto 0);
    SODIMM0_ODT      : out   std_logic_vector(2-1 downto 0);
    SODIMM0_NRST     : out   std_logic;
    SODIMM0_PAR      : out   std_logic;
    SODIMM0_NALERT   : in    std_logic;
    SODIMM0_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM0_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM0_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM0_DQ       : inout std_logic_vector(64-1 downto 0);
    SODIMM0_CHKB     : inout std_logic_vector(8-1 downto 0);
    -- SODIMM1 port
    SODIMM1_REFCLK_P : in    std_logic; -- 33.333 MHz
    SODIMM1_OCT_RZQ  : in    std_logic;
    SODIMM1_PCK      : out   std_logic_vector(2-1 downto 0);
    SODIMM1_NCK      : out   std_logic_vector(2-1 downto 0);
    SODIMM1_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM1_NACT     : out   std_logic;
    SODIMM1_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM1_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM1_CKE      : out   std_logic_vector(2-1 downto 0);
    SODIMM1_NCS      : out   std_logic_vector(2-1 downto 0);
    SODIMM1_ODT      : out   std_logic_vector(2-1 downto 0);
    SODIMM1_NRST     : out   std_logic;
    SODIMM1_PAR      : out   std_logic;
    SODIMM1_NALERT   : in    std_logic;
    SODIMM1_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM1_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM1_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM1_DQ       : inout std_logic_vector(64-1 downto 0);
    SODIMM1_CHKB     : inout std_logic_vector(8-1 downto 0);

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
    HPS_DDR4_REFCLK_P : in    std_logic; -- 33.333 MHz
    HPS_DDR4_OCT_RZQ  : in    std_logic;
    HPS_DDR4_DQ       : inout std_logic_vector(64-1 downto 0);
    HPS_DDR4_DQS      : inout std_logic_vector(8-1 downto 0);
    HPS_DDR4_DQS_N    : inout std_logic_vector(8-1 downto 0);
    HPS_DDR4_DBI_N    : inout std_logic_vector(8-1 downto 0);
    HPS_DDR4_BA       : out   std_logic_vector(2-1 downto 0);
    HPS_DDR4_BG       : out   std_logic_vector(1-1 downto 0);
    HPS_DDR4_ADDR     : out   std_logic_vector(17-1 downto 0);
    HPS_DDR4_ALERT_N  : in    std_logic;
    HPS_DDR4_RST_N    : out   std_logic;
    HPS_DDR4_CS_N     : out   std_logic;
    HPS_DDR4_ACT_N    : out   std_logic;
    HPS_DDR4_ODT_N    : out   std_logic;
    HPS_DDR4_CKE      : out   std_logic;
    HPS_DDR4_CK       : out   std_logic;
    HPS_DDR4_CK_N     : out   std_logic;
    HPS_DDR4_PAR      : out   std_logic
);
end entity;

architecture FULL of FPGA is

    component OnBoard_DDR4 is
    port (
        local_reset_req      : in    std_logic                       := 'X';             -- local_reset_req
        local_reset_done     : out   std_logic;                                          -- local_reset_done
        pll_ref_clk          : in    std_logic                       := 'X';             -- clk
        pll_locked           : out   std_logic;                                          -- pll_locked
        oct_rzqin            : in    std_logic                       := 'X';             -- oct_rzqin
        mem_ck               : out   std_logic_vector(0 downto 0);                       -- mem_ck
        mem_ck_n             : out   std_logic_vector(0 downto 0);                       -- mem_ck_n
        mem_a                : out   std_logic_vector(16 downto 0);                      -- mem_a
        mem_act_n            : out   std_logic_vector(0 downto 0);                       -- mem_act_n
        mem_ba               : out   std_logic_vector(1 downto 0);                       -- mem_ba
        mem_bg               : out   std_logic_vector(0 downto 0);                       -- mem_bg
        mem_cke              : out   std_logic_vector(0 downto 0);                       -- mem_cke
        mem_cs_n             : out   std_logic_vector(0 downto 0);                       -- mem_cs_n
        mem_odt              : out   std_logic_vector(0 downto 0);                       -- mem_odt
        mem_reset_n          : out   std_logic_vector(0 downto 0);                       -- mem_reset_n
        mem_par              : out   std_logic_vector(0 downto 0);                       -- mem_par
        mem_alert_n          : in    std_logic_vector(0 downto 0)    := (others => 'X'); -- mem_alert_n
        mem_dqs              : inout std_logic_vector(7 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n            : inout std_logic_vector(7 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq               : inout std_logic_vector(63 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n            : inout std_logic_vector(7 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success    : out   std_logic;                                          -- local_cal_success
        local_cal_fail       : out   std_logic;                                          -- local_cal_fail
        emif_usr_reset_n     : out   std_logic;                                          -- reset_n
        emif_usr_clk         : out   std_logic;                                          -- clk
        amm_ready_0          : out   std_logic;                                          -- waitrequest_n
        amm_read_0           : in    std_logic                       := 'X';             -- read
        amm_write_0          : in    std_logic                       := 'X';             -- write
        amm_address_0        : in    std_logic_vector(25 downto 0)   := (others => 'X'); -- address
        amm_readdata_0       : out   std_logic_vector(511 downto 0);                     -- readdata
        amm_writedata_0      : in    std_logic_vector(511 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0     : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_byteenable_0     : in    std_logic_vector(63 downto 0)   := (others => 'X'); -- byteenable
        amm_readdatavalid_0  : out   std_logic;                                          -- readdatavalid
        calbus_read          : in    std_logic                       := 'X';             -- calbus_read
        calbus_write         : in    std_logic                       := 'X';             -- calbus_write
        calbus_address       : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
        calbus_wdata         : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
        calbus_rdata         : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
        calbus_seq_param_tbl : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
        calbus_clk           : in    std_logic                       := 'X'              -- clk
    );
    end component OnBoard_DDR4;

    component sodimm is
    port (
        local_reset_req           : in    std_logic                       := 'X';             -- local_reset_req
        local_reset_done          : out   std_logic;                                          -- local_reset_done
        pll_ref_clk               : in    std_logic                       := 'X';             -- clk
        pll_locked                : out   std_logic;                                          -- pll_locked
        oct_rzqin                 : in    std_logic                       := 'X';             -- oct_rzqin
        mem_ck                    : out   std_logic_vector(1 downto 0);                       -- mem_ck
        mem_ck_n                  : out   std_logic_vector(1 downto 0);                       -- mem_ck_n
        mem_a                     : out   std_logic_vector(16 downto 0);                      -- mem_a
        mem_act_n                 : out   std_logic_vector(0 downto 0);                       -- mem_act_n
        mem_ba                    : out   std_logic_vector(1 downto 0);                       -- mem_ba
        mem_bg                    : out   std_logic_vector(1 downto 0);                       -- mem_bg
        mem_cke                   : out   std_logic_vector(1 downto 0);                       -- mem_cke
        mem_cs_n                  : out   std_logic_vector(1 downto 0);                       -- mem_cs_n
        mem_odt                   : out   std_logic_vector(1 downto 0);                       -- mem_odt
        mem_reset_n               : out   std_logic_vector(0 downto 0);                       -- mem_reset_n
        mem_par                   : out   std_logic_vector(0 downto 0);                       -- mem_par
        mem_alert_n               : in    std_logic_vector(0 downto 0)    := (others => 'X'); -- mem_alert_n
        mem_dqs                   : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n                 : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq                    : inout std_logic_vector(71 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n                 : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success         : out   std_logic;                                          -- local_cal_success
        local_cal_fail            : out   std_logic;                                          -- local_cal_fail
        emif_usr_reset_n          : out   std_logic;                                          -- reset_n
        emif_usr_clk              : out   std_logic;                                          -- clk
        amm_ready_0               : out   std_logic;                                          -- waitrequest_n
        amm_read_0                : in    std_logic                       := 'X';             -- read
        amm_write_0               : in    std_logic                       := 'X';             -- write
        amm_address_0             : in    std_logic_vector(28 downto 0)   := (others => 'X'); -- address
        amm_readdata_0            : out   std_logic_vector(575 downto 0);                     -- readdata
        amm_writedata_0           : in    std_logic_vector(575 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_byteenable_0          : in    std_logic_vector(71 downto 0)   := (others => 'X'); -- byteenable
        amm_readdatavalid_0       : out   std_logic;                                          -- readdatavalid
        ctrl_auto_precharge_req_0 : in    std_logic                       := 'X';             -- ctrl_auto_precharge_req
        calbus_read               : in    std_logic                       := 'X';             -- calbus_read
        calbus_write              : in    std_logic                       := 'X';             -- calbus_write
        calbus_address            : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
        calbus_wdata              : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
        calbus_rdata              : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
        calbus_seq_param_tbl      : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
        calbus_clk                : in    std_logic                       := 'X'              -- clk
    );
    end component sodimm;

    component sodimm_cal is
    port (
        calbus_read_0           : out std_logic;                                          -- calbus_read
        calbus_write_0          : out std_logic;                                          -- calbus_write
        calbus_address_0        : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_0          : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_0          : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_0  : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_read_1           : out std_logic;                                          -- calbus_read
        calbus_write_1          : out std_logic;                                          -- calbus_write
        calbus_address_1        : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_1          : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_1          : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_1  : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_clk              : out std_logic;                                          -- clk
        cal_debug_clk_clk       : in  std_logic                       := 'X';             -- clk
        cal_debug_reset_n_reset : in  std_logic                       := 'X'              -- reset
    );
    end component sodimm_cal;
    
    component emif_agi027_cal is
    port (
        calbus_read_0           : out std_logic;                                          -- calbus_read
        calbus_write_0          : out std_logic;                                          -- calbus_write
        calbus_address_0        : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_0          : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_0          : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_0  : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_clk              : out std_logic;                                          -- clk
        cal_debug_clk_clk       : in  std_logic                       := 'X';             -- clk
        cal_debug_reset_n_reset : in  std_logic                       := 'X'              -- reset
    );
    end component emif_agi027_cal;

    function f_dma_endpoints(PCIE_ENDPOINTS : natural; PCIE_EP_MODE : natural; PCIE_GEN : natural) return natural is
        variable dma_ep_v : natural;
    begin
        dma_ep_v := PCIE_ENDPOINTS;
        if (PCIE_EP_MODE = 0) then
            dma_ep_v := 2*dma_ep_v;
        end if;
        if (PCIE_GEN = 5) then
            dma_ep_v := 2*dma_ep_v;
        end if;
        return dma_ep_v;
    end function;

    constant PCIE_LANES      : integer := 16;
    constant PCIE_CLKS       : integer := 2;
    constant PCIE_CONS       : integer := 2;
    constant MISC_IN_WIDTH   : integer := 64;
    constant MISC_OUT_WIDTH  : integer := 64 + 5;
    constant ETH_LANES       : integer := 8;
    constant DMA_ENDPOINTS   : integer := f_dma_endpoints(PCIE_ENDPOINTS,PCIE_ENDPOINT_MODE,PCIE_GEN);
    constant USE_SODIMM_MEM  : boolean := not TEST_FW_PCIE1_ONBOARD_DDR4;
    constant MEM_PORTS       : integer := tsel(USE_SODIMM_MEM,2,1);
    constant MEM_ADDR_WIDTH  : integer := tsel(USE_SODIMM_MEM,29,26); --HPS:26, SODIMM:29;
    constant MEM_DATA_WIDTH  : integer := 512;
    constant MEM_BURST_WIDTH : integer := 7;
    constant AMM_FREQ_KHZ    : integer := 333333; --HPS:3333325, SODIMM:3333325;
    constant DEVICE          : string  := "AGILEX";

    signal pcie_ext_clk0_p        : std_logic;
    signal pcie_ext_clk1_p        : std_logic;
    signal pcie_ext_perst_n       : std_logic;
    signal pcie_ext_rx_p          : std_logic_vector(15 downto 0);
    signal pcie_ext_rx_n          : std_logic_vector(15 downto 0);
    signal pcie_ext_tx_p          : std_logic_vector(15 downto 0);
    signal pcie_ext_tx_n          : std_logic_vector(15 downto 0);
 
    signal calbus_read            : std_logic_vector(MEM_PORTS-1 downto 0);
    signal calbus_write           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal calbus_address         : slv_array_t(MEM_PORTS-1 downto 0)(19 downto 0);
    signal calbus_wdata           : slv_array_t(MEM_PORTS-1 downto 0)(31 downto 0);
    signal calbus_rdata           : slv_array_t(MEM_PORTS-1 downto 0)(31 downto 0);
    signal calbus_seq_param_tbl   : slv_array_t(MEM_PORTS-1 downto 0)(4095 downto 0);
    signal calbus_clk             : std_logic_vector(MEM_PORTS-1 downto 0);

    signal mem_clk                : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_rst                : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_rst_n              : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_pll_locked         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_pll_locked_sync    : std_logic_vector(MEM_PORTS-1 downto 0);
    
    signal mem_avmm_ready         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_read          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_write         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_address       : slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal mem_avmm_burstcount    : slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal mem_avmm_writedata     : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdata      : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_writedata_f   : slv_array_t(MEM_PORTS-1 downto 0)(576-1 downto 0) := (others => (others => '0'));
    signal mem_avmm_readdata_f    : slv_array_t(MEM_PORTS-1 downto 0)(576-1 downto 0) := (others => (others => '0'));
    signal mem_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0);
     
    signal emif_rst_req           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_ecc_usr_int       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_success       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_fail          : std_logic_vector(MEM_PORTS-1 downto 0);

    signal misc_in                : std_logic_vector(MISC_IN_WIDTH-1 downto 0);
    signal misc_out               : std_logic_vector(MISC_OUT_WIDTH-1 downto 0);

    signal pcie_clk               : std_logic;
    signal pcie_reset             : std_logic;

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

    signal boot_request           : std_logic;
    signal boot_image             : std_logic;

    signal flash_wr_data          : std_logic_vector(63 downto 0);
    signal flash_rd_data          : std_logic_vector(63 downto 0);
    signal flash_wr_en            : std_logic;
    signal flash_d_i              : std_logic_vector(15 downto 0);
    signal flash_d_o              : std_logic_vector(15 downto 0);
    signal flash_d_oe             : std_logic;
    signal flash_d_oe_n           : std_logic;
    signal flash_ce_n             : std_logic;

begin

    AG_I2C_SCLK	<= 'Z';
    AG_I2C_SDA	<= 'Z';
    
    AG_SOFT_RST  <= '0';
    AG_M10_RST_N <= '1';

    AG_M10_IMG_SEL_N <= '1';
    -- Must not be permanently assigned to GND!
    AG_M10_REBOOT_N  <= '1';

    AG_CFG_IMG_SEL <= boot_image;
    AG_REQ_CONF_N  <= not boot_request;

    PCIE1_CLK_SEL_N	<= '1';
    PCIE2_CLK_SEL_N	<= '1';

    pcie_ext_g : if not TEST_FW_PCIE1_ONBOARD_DDR4 generate
        pcie_ext_clk0_p  <= PCIE2_CLK0_P;
        pcie_ext_clk1_p  <= PCIE2_CLK1_P;
        pcie_ext_perst_n <= PCIE2_PERST_N;
        pcie_ext_rx_p    <= PCIE2_RX_P;
        pcie_ext_rx_n    <= PCIE2_RX_N;
        PCIE2_TX_P       <= pcie_ext_tx_p;
        PCIE2_TX_N       <= pcie_ext_tx_n;
    else generate
        pcie_ext_clk0_p  <= PCIE1_CLK0_P;
        pcie_ext_clk1_p  <= PCIE1_CLK1_P;
        pcie_ext_perst_n <= PCIE1_PERST_N;
        pcie_ext_rx_p    <= PCIE1_RX_P;
        pcie_ext_rx_n    <= PCIE1_RX_N;
        PCIE1_TX_P       <= pcie_ext_tx_p;
        PCIE1_TX_N       <= pcie_ext_tx_n;
    end generate;

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

        PCI_VENDOR_ID           => X"18EC",
        PCI_DEVICE_ID           => X"C400",
        PCI_SUBVENDOR_ID        => X"0000",
        PCI_SUBDEVICE_ID        => X"0000",
        
        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => 8,
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => ETH_PORTS,
        QSFP_I2C_PORTS          => ETH_PORTS,

        MEM_PORTS               => MEM_PORTS,
        MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH,
        MEM_DATA_WIDTH          => MEM_DATA_WIDTH,
        MEM_BURST_WIDTH         => MEM_BURST_WIDTH,
        AMM_FREQ_KHZ            => AMM_FREQ_KHZ,

        STATUS_LEDS             => 2,

        MISC_IN_WIDTH           => MISC_IN_WIDTH,
        MISC_OUT_WIDTH          => MISC_OUT_WIDTH,

        BOARD                   => CARD_NAME,
        DEVICE                  => DEVICE,

        PCIE_ENDPOINTS          => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE      => PCIE_MOD_ARCH,
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,

        DMA_ENDPOINTS           => DMA_ENDPOINTS,
        DMA_MODULES             => 1,
        DMA_RX_CHANNELS         => DMA_RX_CHANNELS,
        DMA_TX_CHANNELS         => DMA_TX_CHANNELS
    )
    port map(
        SYSCLK                  => AG_SYSCLK1_P,
        SYSRST                  => '0',

        PCIE_SYSCLK_P           => pcie_ext_clk1_p & pcie_ext_clk0_p & PCIE0_CLK1_P & PCIE0_CLK0_P,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N           => pcie_ext_perst_n & PCIE0_PERST_N,

        PCIE_RX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_RX_P,
        PCIE_RX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => pcie_ext_rx_p,
        PCIE_RX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_RX_N,
        PCIE_RX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => pcie_ext_rx_n,

        PCIE_TX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_TX_P,
        PCIE_TX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => pcie_ext_tx_p,
        PCIE_TX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_TX_N,
        PCIE_TX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => pcie_ext_tx_n,

        ETH_REFCLK_P(0)         => QSFP_REFCLK0_P,
        ETH_REFCLK_N(0)         => '0',
        ETH_RX_P                => QSFP_RX_P,
        ETH_RX_N                => QSFP_RX_N,
        ETH_TX_P                => QSFP_TX_P,
        ETH_TX_N                => QSFP_TX_N,

        ETH_LED_R               => QSFP_LED_R,
        ETH_LED_G               => QSFP_LED_G,

        QSFP_I2C_SCL(0)         => QSFP_I2C_SCL,
        QSFP_I2C_SDA(0)         => QSFP_I2C_SDA,

        QSFP_MODSEL_N(0)        => QSFP_MODSEL_N,
        QSFP_LPMODE(0)          => QSFP_INITMODE,
        QSFP_RESET_N(0)         => QSFP_RST_N,
        QSFP_MODPRS_N(0)        => QSFP_MODPRS_N,
        QSFP_INT_N(0)           => QSFP_INT_N,

        MEM_CLK                 => mem_clk,
        MEM_RST                 => mem_rst,

        MEM_AVMM_READY          => mem_avmm_ready,
        MEM_AVMM_READ           => mem_avmm_read,
        MEM_AVMM_WRITE          => mem_avmm_write,
        MEM_AVMM_ADDRESS        => mem_avmm_address,
        MEM_AVMM_BURSTCOUNT     => mem_avmm_burstcount,
        MEM_AVMM_WRITEDATA      => mem_avmm_writedata,
        MEM_AVMM_READDATA       => mem_avmm_readdata,
        MEM_AVMM_READDATAVALID  => mem_avmm_readdatavalid,

        EMIF_RST_REQ            => emif_rst_req,
        EMIF_RST_DONE           => emif_rst_done,
        EMIF_ECC_USR_INT        => emif_ecc_usr_int,
        EMIF_CAL_SUCCESS        => emif_cal_success,
        EMIF_CAL_FAIL           => emif_cal_fail,

        STATUS_LED_G            => AG_LED_G,
        STATUS_LED_R            => AG_LED_R,

        PCIE_CLK                => pcie_clk,
        PCIE_RESET              => pcie_reset,
    
        BOOT_MI_CLK             => boot_mi_clk,
        BOOT_MI_RESET           => boot_mi_reset,
        BOOT_MI_DWR             => boot_mi_dwr,
        BOOT_MI_ADDR            => boot_mi_addr,
        BOOT_MI_RD              => boot_mi_rd,
        BOOT_MI_WR              => boot_mi_wr,
        BOOT_MI_BE              => boot_mi_be,
        BOOT_MI_DRD             => boot_mi_drd,
        BOOT_MI_ARDY            => boot_mi_ardy,
        BOOT_MI_DRDY            => boot_mi_drdy,

        MISC_IN                 => misc_in,
        MISC_OUT                => misc_out
    );

    -- ---------------------------------------------------------------------------

    boot_ctrl_i : entity work.BOOT_CTRL
    generic map(
        DEVICE      => DEVICE,
        BOOT_TYPE   => 2
    )
    port map(
        MI_CLK        => boot_mi_clk,
        MI_RESET      => boot_mi_reset,
        MI_DWR        => boot_mi_dwr,
        MI_ADDR       => boot_mi_addr,
        MI_BE         => boot_mi_be,
        MI_RD         => boot_mi_rd,
        MI_WR         => boot_mi_wr,
        MI_ARDY       => boot_mi_ardy,
        MI_DRD        => boot_mi_drd,
        MI_DRDY       => boot_mi_drdy,

        BOOT_CLK      => pcie_clk,
        BOOT_RESET    => pcie_reset,

        BOOT_REQUEST  => boot_request,
        BOOT_IMAGE    => boot_image,

        FLASH_WR_DATA => flash_wr_data,
        FLASH_WR_EN   => flash_wr_en,
        FLASH_RD_DATA => flash_rd_data
    ); 

    FLASHCTRL_I: entity work.flashctrl
    generic map (
        CLK_PERIOD => 2 -- Clock period time in ns
    )
    port map (
        RESET  => pcie_reset,
        CLK    => pcie_clk,
        -- Command interface
        DWR    => flash_wr_data,
        DWR_WR => flash_wr_en,
        DRD    => flash_rd_data,
        -- FLASH interface
        AD     => FLASH_A,
        D_I    => FLASH_D,
        D_O    => flash_d_o,
        D_OE   => flash_d_oe,
        CS_N   => flash_ce_n,
        OE_N   => FLASH_OE_N,
        RST_N  => open,
        WE_N   => FLASH_WE_N
    );

    FLASH_D     <= flash_d_o when flash_d_oe = '1' else (others => 'Z');
    -- flash_wr_data(59) is the highest address bit. It is used to select beetween FLASH0 and FLASH1 chips
    FLASH_CE0_N <= flash_ce_n or (flash_wr_data(59));
    FLASH_CE1_N <= flash_ce_n or (not flash_wr_data(59));

    -- ---------------------------------------------------------------------------

    mem_rst_g : for i in 0 to MEM_PORTS-1 generate
        mem_pll_locked_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => false
        )
        port map(
            ACLK     => '0',
            BCLK     => mem_clk(i),
            ARST     => '0',
            BRST     => '0',
            ADATAIN  => mem_pll_locked(i),
            BDATAOUT => mem_pll_locked_sync(i)
        );

        mem_rst(i) <= not mem_rst_n(i); -- and mem_pll_locked_sync(i));
    end generate;

    sodimm_g: if USE_SODIMM_MEM generate
        sodimm0_i : component sodimm
        port map (
            local_reset_req           => emif_rst_req(0),
            local_reset_done          => emif_rst_done(0),
            pll_ref_clk               => SODIMM0_REFCLK_P,
            pll_locked                => mem_pll_locked(0),
            oct_rzqin                 => SODIMM0_OCT_RZQ,
            mem_ck                    => SODIMM0_PCK,
            mem_ck_n                  => SODIMM0_NCK,
            mem_a                     => SODIMM0_A,
            mem_act_n(0)              => SODIMM0_NACT,
            mem_ba                    => SODIMM0_BA,
            mem_bg                    => SODIMM0_BG,
            mem_cke                   => SODIMM0_CKE,
            mem_cs_n                  => SODIMM0_NCS,
            mem_odt                   => SODIMM0_ODT,
            mem_reset_n(0)            => SODIMM0_NRST,
            mem_par(0)                => SODIMM0_PAR,
            mem_alert_n(0)            => SODIMM0_NALERT,
            mem_dqs                   => SODIMM0_PDQS,
            mem_dqs_n                 => SODIMM0_NDQS,
            mem_dq(63 downto 0)       => SODIMM0_DQ,
            mem_dq(71 downto 64)      => SODIMM0_CHKB,
            mem_dbi_n                 => SODIMM0_DM_DBI,
            local_cal_success         => emif_cal_success(0),
            local_cal_fail            => emif_cal_fail(0),              
            emif_usr_reset_n          => mem_rst_n(0), 
            emif_usr_clk              => mem_clk(0),
            amm_ready_0               => mem_avmm_ready(0),
            amm_read_0                => mem_avmm_read(0),
            amm_write_0               => mem_avmm_write(0),
            amm_address_0             => mem_avmm_address(0),
            amm_readdata_0            => mem_avmm_readdata_f(0),
            amm_writedata_0           => mem_avmm_writedata_f(0),
            amm_burstcount_0          => mem_avmm_burstcount(0),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(0),
            amm_byteenable_0          => (others => '1'),
            calbus_read               => calbus_read(0),   
            calbus_write              => calbus_write(0),  
            calbus_address            => calbus_address(0),
            calbus_wdata              => calbus_wdata(0),  
            calbus_rdata              => calbus_rdata(0),  
            calbus_seq_param_tbl      => calbus_seq_param_tbl(0), 
            calbus_clk                => calbus_clk(0)
        );

        sodimm1_i : component sodimm
        port map (
            local_reset_req           => emif_rst_req(1),
            local_reset_done          => emif_rst_done(1),
            pll_ref_clk               => SODIMM1_REFCLK_P,
            pll_locked                => mem_pll_locked(1),
            oct_rzqin                 => SODIMM1_OCT_RZQ,
            mem_ck                    => SODIMM1_PCK,
            mem_ck_n                  => SODIMM1_NCK,
            mem_a                     => SODIMM1_A,
            mem_act_n(0)              => SODIMM1_NACT,
            mem_ba                    => SODIMM1_BA,
            mem_bg                    => SODIMM1_BG,
            mem_cke                   => SODIMM1_CKE,
            mem_cs_n                  => SODIMM1_NCS,
            mem_odt                   => SODIMM1_ODT,
            mem_reset_n(0)            => SODIMM1_NRST,
            mem_par(0)                => SODIMM1_PAR,
            mem_alert_n(0)            => SODIMM1_NALERT,
            mem_dqs                   => SODIMM1_PDQS,
            mem_dqs_n                 => SODIMM1_NDQS,
            mem_dq(63 downto 0)       => SODIMM1_DQ,
            mem_dq(71 downto 64)      => SODIMM1_CHKB,
            mem_dbi_n                 => SODIMM1_DM_DBI,
            local_cal_success         => emif_cal_success(1),
            local_cal_fail            => emif_cal_fail(1),              
            emif_usr_reset_n          => mem_rst_n(1), 
            emif_usr_clk              => mem_clk(1),
            amm_ready_0               => mem_avmm_ready(1),
            amm_read_0                => mem_avmm_read(1),
            amm_write_0               => mem_avmm_write(1),
            amm_address_0             => mem_avmm_address(1),
            amm_readdata_0            => mem_avmm_readdata_f(1),
            amm_writedata_0           => mem_avmm_writedata_f(1),
            amm_burstcount_0          => mem_avmm_burstcount(1),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(1),
            amm_byteenable_0          => (others => '1'),
            calbus_read               => calbus_read(1),   
            calbus_write              => calbus_write(1),  
            calbus_address            => calbus_address(1),
            calbus_wdata              => calbus_wdata(1),  
            calbus_rdata              => calbus_rdata(1),  
            calbus_seq_param_tbl      => calbus_seq_param_tbl(1), 
            calbus_clk                => calbus_clk(1)
        );

        sodimm_cal_i : component sodimm_cal
        port map (
            calbus_read_0           => calbus_read(0),
            calbus_write_0          => calbus_write(0),
            calbus_address_0        => calbus_address(0),
            calbus_wdata_0          => calbus_wdata(0),
            calbus_rdata_0          => calbus_rdata(0),
            calbus_seq_param_tbl_0  => calbus_seq_param_tbl(0),
            calbus_read_1           => calbus_read(1),
            calbus_write_1          => calbus_write(1),
            calbus_address_1        => calbus_address(1),
            calbus_wdata_1          => calbus_wdata(1),
            calbus_rdata_1          => calbus_rdata(1),
            calbus_seq_param_tbl_1  => calbus_seq_param_tbl(1),
            calbus_clk              => calbus_clk(0),
            cal_debug_clk_clk       => mem_clk(0),
            cal_debug_reset_n_reset => mem_rst_n(0)
        );

        mem_avmm_writedata_f(0)(MEM_DATA_WIDTH-1 downto 0)   <= mem_avmm_writedata(0);
        mem_avmm_writedata_f(1)(MEM_DATA_WIDTH-1 downto 0)   <= mem_avmm_writedata(1);
        mem_avmm_readdata(0) <= mem_avmm_readdata_f(0)(MEM_DATA_WIDTH-1 downto 0);
        mem_avmm_readdata(1) <= mem_avmm_readdata_f(1)(MEM_DATA_WIDTH-1 downto 0);

        HPS_DDR4_DQ    <= (others => 'Z');
        HPS_DDR4_DQS   <= (others => 'Z');
        HPS_DDR4_DQS_N <= (others => 'Z');
        HPS_DDR4_DBI_N <= (others => 'Z');
        HPS_DDR4_BA    <= (others => 'Z');
        HPS_DDR4_BG    <= (others => 'Z');
        HPS_DDR4_ADDR  <= (others => 'Z');
        HPS_DDR4_RST_N <= 'Z';
        HPS_DDR4_CS_N  <= 'Z';
        HPS_DDR4_ACT_N <= 'Z';
        HPS_DDR4_ODT_N <= 'Z';
        HPS_DDR4_CKE   <= 'Z';
        HPS_DDR4_CK    <= 'Z';
        HPS_DDR4_CK_N  <= 'Z';
        HPS_DDR4_PAR   <= 'Z';
    end generate;

    onboard_ddr4_g: if not USE_SODIMM_MEM generate
        onboard_ddr4_i : component OnBoard_DDR4
        port map (
            local_reset_req      => emif_rst_req(0),
            local_reset_done     => emif_rst_done(0),
            pll_ref_clk          => HPS_DDR4_REFCLK_P,
            pll_locked           => mem_pll_locked(0),
            oct_rzqin            => HPS_DDR4_OCT_RZQ,
            mem_ck(0)            => HPS_DDR4_CK,
            mem_ck_n(0)          => HPS_DDR4_CK_N,
            mem_a                => HPS_DDR4_ADDR,
            mem_act_n(0)         => HPS_DDR4_ACT_N,
            mem_ba               => HPS_DDR4_BA,
            mem_bg               => HPS_DDR4_BG,
            mem_cke(0)           => HPS_DDR4_CKE,
            mem_cs_n(0)          => HPS_DDR4_CS_N,
            mem_odt(0)           => HPS_DDR4_ODT_N,
            mem_reset_n(0)       => HPS_DDR4_RST_N,
            mem_par(0)           => HPS_DDR4_PAR,
            mem_alert_n(0)       => HPS_DDR4_ALERT_N,
            mem_dqs              => HPS_DDR4_DQS,
            mem_dqs_n            => HPS_DDR4_DQS_N,
            mem_dq               => HPS_DDR4_DQ,
            mem_dbi_n            => HPS_DDR4_DBI_N,
            local_cal_success    => emif_cal_success(0),
            local_cal_fail       => emif_cal_fail(0),
            emif_usr_reset_n     => mem_rst_n(0),
            emif_usr_clk         => mem_clk(0),
            amm_ready_0          => mem_avmm_ready(0),
            amm_read_0           => mem_avmm_read(0),
            amm_write_0          => mem_avmm_write(0),
            amm_address_0        => mem_avmm_address(0),
            amm_readdata_0       => mem_avmm_readdata(0),
            amm_writedata_0      => mem_avmm_writedata(0),
            amm_burstcount_0     => mem_avmm_burstcount(0),
            amm_byteenable_0     => (others => '1'),
            amm_readdatavalid_0  => mem_avmm_readdatavalid(0),
            calbus_read          => calbus_read(0),
            calbus_write         => calbus_write(0),
            calbus_address       => calbus_address(0),
            calbus_wdata         => calbus_wdata(0),
            calbus_rdata         => calbus_rdata(0),
            calbus_seq_param_tbl => calbus_seq_param_tbl(0),
            calbus_clk           => calbus_clk(0)
        );

        emif_cal_i : component emif_agi027_cal
        port map (
            calbus_read_0               => calbus_read(0),              
            calbus_write_0              => calbus_write(0),       
            calbus_address_0            => calbus_address(0),     
            calbus_wdata_0              => calbus_wdata(0),    
            calbus_rdata_0              => calbus_rdata(0),       
            calbus_seq_param_tbl_0      => calbus_seq_param_tbl(0),
            calbus_clk                  => calbus_clk(0),
            cal_debug_clk_clk           => mem_clk(0),
            cal_debug_reset_n_reset     => mem_rst_n(0)
        );

        SODIMM0_NACT   <= 'Z';
        SODIMM0_NRST   <= 'Z';
        SODIMM0_PAR    <= 'Z';
        SODIMM0_PCK    <= (others => 'Z');
        SODIMM0_NCK    <= (others => 'Z');
        SODIMM0_A      <= (others => 'Z');
        SODIMM0_BA     <= (others => 'Z');
        SODIMM0_BG     <= (others => 'Z');
        SODIMM0_CKE    <= (others => 'Z');
        SODIMM0_NCS    <= (others => 'Z');
        SODIMM0_ODT    <= (others => 'Z');
        SODIMM0_PDQS   <= (others => 'Z');
        SODIMM0_NDQS   <= (others => 'Z');
        SODIMM0_DM_DBI <= (others => 'Z');
        SODIMM0_DQ     <= (others => 'Z');
        SODIMM0_CHKB   <= (others => 'Z');

        SODIMM1_NACT   <= 'Z';
        SODIMM1_NRST   <= 'Z';
        SODIMM1_PAR    <= 'Z';
        SODIMM1_PCK    <= (others => 'Z');
        SODIMM1_NCK    <= (others => 'Z');
        SODIMM1_A      <= (others => 'Z');
        SODIMM1_BA     <= (others => 'Z');
        SODIMM1_BG     <= (others => 'Z');
        SODIMM1_CKE    <= (others => 'Z');
        SODIMM1_NCS    <= (others => 'Z');
        SODIMM1_ODT    <= (others => 'Z');
        SODIMM1_PDQS   <= (others => 'Z');
        SODIMM1_NDQS   <= (others => 'Z');
        SODIMM1_DM_DBI <= (others => 'Z');
        SODIMM1_DQ     <= (others => 'Z');
        SODIMM1_CHKB   <= (others => 'Z');
    end generate;

end architecture;
