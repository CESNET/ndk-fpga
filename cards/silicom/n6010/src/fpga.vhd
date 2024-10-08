-- fpga.vhd: N6010 board top level entity and architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Martin Matějka <xmatej55@vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
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

    -- =========================================================================
    -- PCIe
    -- =========================================================================
    PCIE_REFCLK0       : in    std_logic;
    PCIE_REFCLK1       : in    std_logic;
    PCIE_SYSRST_N      : in    std_logic;
    PCIE_RX_P          : in    std_logic_vector(15 downto 0);
    PCIE_RX_N          : in    std_logic_vector(15 downto 0);
    PCIE_TX_P          : out   std_logic_vector(15 downto 0);
    PCIE_TX_N          : out   std_logic_vector(15 downto 0);

    -- =========================================================================
    -- QSFP
    -- =========================================================================
    QSFP_REFCLK_156M    : in    std_logic;

    -- QSFP data
    QSFP0_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP0_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP0_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP0_TX_N          : out   std_logic_vector(4-1 downto 0);

    QSFP1_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP1_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP1_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP1_TX_N          : out   std_logic_vector(4-1 downto 0);

    -- QSFP control
    QSFP0_I2C_SCL       : inout std_logic;
    QSFP0_I2C_SDA       : inout std_logic;
    QSFP0_LPMODE        : out   std_logic;
    QSFP0_RESET_N       : out   std_logic;
    QSFP0_MODESEL_N     : out   std_logic;
    QSFP0_MODPRS_N      : in    std_logic;
    QSFP0_INT_N         : in    std_logic;

    QSFP1_I2C_SCL       : inout std_logic;
    QSFP1_I2C_SDA       : inout std_logic;
    QSFP1_LPMODE        : out   std_logic;
    QSFP1_RESET_N       : out   std_logic;
    QSFP1_MODESEL_N     : out   std_logic;
    QSFP1_MODPRS_N      : in    std_logic;
    QSFP1_INT_N         : in    std_logic;

    -- QSFP leds
    QSFP0_LED_G         : out   std_logic;
    QSFP0_LED_R         : out   std_logic;
    QSFP1_LED_G         : out   std_logic;
    QSFP1_LED_R         : out   std_logic;

    -- =========================================================================
    -- DDR4 Channel 0
    -- =========================================================================
    DDR4_CH0_REF_CLK   : in    std_logic;
    DDR4_CH0_OCT_RZQIN : in    std_logic;
    DDR4_CH0_ALERT_N   : in    std_logic;
    DDR4_CH0_BG        : out   std_logic;
    DDR4_CH0_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH0_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH0_PAR       : out   std_logic;
    DDR4_CH0_CK_N      : out   std_logic;
    DDR4_CH0_CK        : out   std_logic;
    DDR4_CH0_CKE       : out   std_logic;
    DDR4_CH0_ODT       : out   std_logic;
    DDR4_CH0_ACT_N     : out   std_logic;
    DDR4_CH0_CS_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_CH0_RESET_N   : out   std_logic;
    DDR4_CH0_DQS       : inout std_logic_vector(4-1 downto 0);
    DDR4_CH0_DQS_N     : inout std_logic_vector(4-1 downto 0);
    DDR4_CH0_DQ        : inout std_logic_vector(32-1 downto 0);
    DDR4_CH0_DBI_N     : inout std_logic_vector(4-1 downto 0);

    -- =========================================================================
    -- DDR4 Channel 1
    -- =========================================================================
    DDR4_CH1_REF_CLK   : in    std_logic;
    DDR4_CH1_OCT_RZQIN : in    std_logic;
    DDR4_CH1_ALERT_N   : in    std_logic;
    DDR4_CH1_BG        : out   std_logic;
    DDR4_CH1_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH1_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH1_PAR       : out   std_logic;
    DDR4_CH1_CK_N      : out   std_logic;
    DDR4_CH1_CK        : out   std_logic;
    DDR4_CH1_CKE       : out   std_logic;
    DDR4_CH1_ODT       : out   std_logic;
    DDR4_CH1_ACT_N     : out   std_logic;
    DDR4_CH1_CS_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_CH1_RESET_N   : out   std_logic;
    DDR4_CH1_DQS       : inout std_logic_vector(4-1 downto 0);
    DDR4_CH1_DQS_N     : inout std_logic_vector(4-1 downto 0);
    DDR4_CH1_DQ        : inout std_logic_vector(32-1 downto 0);
    DDR4_CH1_DBI_N     : inout std_logic_vector(4-1 downto 0);

    -- =========================================================================
    -- DDR4 Channel 2
    -- =========================================================================
    DDR4_CH2_REF_CLK   : in    std_logic;
    DDR4_CH2_OCT_RZQIN : in    std_logic;
    DDR4_CH2_ALERT_N   : in    std_logic;
    DDR4_CH2_BG        : out   std_logic;
    DDR4_CH2_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH2_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH2_PAR       : out   std_logic;
    DDR4_CH2_CK_N      : out   std_logic;
    DDR4_CH2_CK        : out   std_logic;
    DDR4_CH2_CKE       : out   std_logic;
    DDR4_CH2_ODT       : out   std_logic;
    DDR4_CH2_ACT_N     : out   std_logic;
    DDR4_CH2_CS_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_CH2_RESET_N   : out   std_logic;
    DDR4_CH2_DQS       : inout std_logic_vector(4-1 downto 0);
    DDR4_CH2_DQS_N     : inout std_logic_vector(4-1 downto 0);
    DDR4_CH2_DQ        : inout std_logic_vector(32-1 downto 0);
    DDR4_CH2_DBI_N     : inout std_logic_vector(4-1 downto 0);

    -- =========================================================================
    -- DDR4 Channel 3
    -- =========================================================================
    DDR4_CH3_REF_CLK   : in    std_logic;
    DDR4_CH3_OCT_RZQIN : in    std_logic;
    DDR4_CH3_ALERT_N   : in    std_logic;
    DDR4_CH3_BG        : out   std_logic;
    DDR4_CH3_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH3_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH3_PAR       : out   std_logic;
    DDR4_CH3_CK_N      : out   std_logic;
    DDR4_CH3_CK        : out   std_logic;
    DDR4_CH3_CKE       : out   std_logic;
    DDR4_CH3_ODT       : out   std_logic;
    DDR4_CH3_ACT_N     : out   std_logic;
    DDR4_CH3_CS_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_CH3_RESET_N   : out   std_logic;
    DDR4_CH3_DQS       : inout std_logic_vector(4-1 downto 0);
    DDR4_CH3_DQS_N     : inout std_logic_vector(4-1 downto 0);
    DDR4_CH3_DQ        : inout std_logic_vector(32-1 downto 0);
    DDR4_CH3_DBI_N     : inout std_logic_vector(4-1 downto 0);

    -- =========================================================================
    -- BMC INTERFACE
    -- =========================================================================
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

architecture FULL of FPGA is

    component ddr4_calibration is
    port (
        calbus_read_0          : out std_logic;                                          -- calbus_read
        calbus_write_0         : out std_logic;                                          -- calbus_write
        calbus_address_0       : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_0         : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_0         : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_0 : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_read_1          : out std_logic;                                          -- calbus_read
        calbus_write_1         : out std_logic;                                          -- calbus_write
        calbus_address_1       : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_1         : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_1         : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_1 : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_clk             : out std_logic                                           -- clk
    );
    end component;

    component onboard_ddr4 is
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
        mem_cs_n             : out   std_logic_vector(1 downto 0);                       -- mem_cs_n
        mem_odt              : out   std_logic_vector(0 downto 0);                       -- mem_odt
        mem_reset_n          : out   std_logic_vector(0 downto 0);                       -- mem_reset_n
        mem_par              : out   std_logic_vector(0 downto 0);                       -- mem_par
        mem_alert_n          : in    std_logic_vector(0 downto 0)    := (others => 'X'); -- mem_alert_n
        mem_dqs              : inout std_logic_vector(3 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n            : inout std_logic_vector(3 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq               : inout std_logic_vector(31 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n            : inout std_logic_vector(3 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success    : out   std_logic;                                          -- local_cal_success
        local_cal_fail       : out   std_logic;                                          -- local_cal_fail
        emif_usr_reset_n     : out   std_logic;                                          -- reset_n
        emif_usr_clk         : out   std_logic;                                          -- clk
        amm_ready_0          : out   std_logic;                                          -- waitrequest_n
        amm_read_0           : in    std_logic                       := 'X';             -- read
        amm_write_0          : in    std_logic                       := 'X';             -- write
        amm_address_0        : in    std_logic_vector(26 downto 0)   := (others => 'X'); -- address
        amm_readdata_0       : out   std_logic_vector(255 downto 0);                     -- readdata
        amm_writedata_0      : in    std_logic_vector(255 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0     : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_readdatavalid_0  : out   std_logic;                                          -- readdatavalid
        calbus_read          : in    std_logic                       := 'X';             -- calbus_read
        calbus_write         : in    std_logic                       := 'X';             -- calbus_write
        calbus_address       : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
        calbus_wdata         : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
        calbus_rdata         : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
        calbus_seq_param_tbl : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
        calbus_clk           : in    std_logic                       := 'X'              -- clk
    );
    end component;

    constant PCIE_LANES      : natural := 16;
    constant PCIE_CLKS       : natural := 2;
    constant PCIE_CONS       : natural := 1;
    constant MISC_IN_WIDTH   : natural := 4;
    constant MISC_OUT_WIDTH  : natural := 4;
    constant ETH_LANES       : natural := 4;
    constant DMA_MODULES     : natural := tsel(DMA_TYPE = 4, 1, ETH_PORTS);
    constant DMA_ENDPOINTS   : natural := tsel(DMA_TYPE = 4 or PCIE_ENDPOINT_MODE=1,PCIE_ENDPOINTS,2*PCIE_ENDPOINTS);
    constant STATUS_LEDS     : natural := 4; -- fake leds

    -- DDR4
    constant MEM_ADDR_WIDTH  : natural := 27;
    constant MEM_DATA_WIDTH  : natural := 256;
    constant MEM_BURST_WIDTH : natural := 7;
    constant AMM_FREQ_KHZ    : natural := 300000;

    signal eth_rx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_rx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    signal eth_refclk_p           : std_logic_vector(ETH_PORTS-1 downto 0);
    signal eth_refclk_n           : std_logic_vector(ETH_PORTS-1 downto 0);

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

    signal calbus_read            : std_logic_vector(MEM_PORTS-1 downto 0);
    signal calbus_write           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal calbus_address         : slv_array_t(MEM_PORTS-1 downto 0)(19 downto 0);
    signal calbus_wdata           : slv_array_t(MEM_PORTS-1 downto 0)(31 downto 0);
    signal calbus_rdata           : slv_array_t(MEM_PORTS-1 downto 0)(31 downto 0);
    signal calbus_seq_param_tbl   : slv_array_t(MEM_PORTS-1 downto 0)(4095 downto 0);
    signal calbus_clk             : std_logic_vector(MEM_PORTS-1 downto 0);

    signal mem_clk                : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal mem_rst_n              : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal mem_pll_locked         : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    
    signal mem_avmm_ready         : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal mem_avmm_read          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_write         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_address       : slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal mem_avmm_burstcount    : slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal mem_avmm_writedata     : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdata      : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    signal mem_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
     
    signal emif_rst_req           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_ecc_usr_int       : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_cal_success       : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_cal_fail          : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '1');

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

        USE_PCIE_CLK            => false,

        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,
        PCIE_CONS               => PCIE_CONS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS, -- two QSFP cages as two ETH ports
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => 1,
        ETH_LANES               => ETH_LANES,
        
        QSFP_PORTS              => ETH_PORTS,
        QSFP_I2C_PORTS          => ETH_PORTS,

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
        AMM_FREQ_KHZ            => AMM_FREQ_KHZ,

        BOARD                   => CARD_NAME,
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
        
        ETH_REFCLK_P           => eth_refclk_p,
        ETH_REFCLK_N           => eth_refclk_n,
        
        ETH_RX_P               => eth_rx_p,
        ETH_RX_N               => eth_rx_n,
        ETH_TX_P               => eth_tx_p,
        ETH_TX_N               => eth_tx_n,

        ETH_LED_R(0)           => QSFP0_LED_R,
        ETH_LED_R(1)           => QSFP1_LED_R,
        ETH_LED_G(0)           => QSFP0_LED_G,
        ETH_LED_G(1)           => QSFP1_LED_G,

        QSFP_I2C_SCL(0)        => QSFP0_I2C_SCL,
        QSFP_I2C_SCL(1)        => QSFP1_I2C_SCL,
        QSFP_I2C_SDA(0)        => QSFP0_I2C_SDA,
        QSFP_I2C_SDA(1)        => QSFP1_I2C_SDA,
        QSFP_MODSEL_N(0)       => QSFP0_MODESEL_N,
        QSFP_MODSEL_N(1)       => QSFP1_MODESEL_N,
        QSFP_LPMODE(0)         => QSFP0_LPMODE,
        QSFP_LPMODE(1)         => QSFP1_LPMODE,
        QSFP_RESET_N(0)        => QSFP0_RESET_N,
        QSFP_RESET_N(1)        => QSFP1_RESET_N,
        QSFP_MODPRS_N          => QSFP1_MODPRS_N & QSFP0_MODPRS_N,
        QSFP_INT_N             => QSFP1_INT_N & QSFP0_INT_N,

        MEM_CLK                => mem_clk,
        MEM_RST                => not mem_rst_n,

        MEM_AVMM_READY         => mem_avmm_ready,
        MEM_AVMM_READ          => mem_avmm_read,
        MEM_AVMM_WRITE         => mem_avmm_write,
        MEM_AVMM_ADDRESS       => mem_avmm_address,
        MEM_AVMM_BURSTCOUNT    => mem_avmm_burstcount,
        MEM_AVMM_WRITEDATA     => mem_avmm_writedata,
        MEM_AVMM_READDATA      => mem_avmm_readdata,
        MEM_AVMM_READDATAVALID => mem_avmm_readdatavalid,

        EMIF_RST_REQ           => emif_rst_req,
        EMIF_RST_DONE          => emif_rst_done,
        EMIF_ECC_USR_INT       => emif_ecc_usr_int,
        EMIF_CAL_SUCCESS       => emif_cal_success,
        EMIF_CAL_FAIL          => emif_cal_fail,
        
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

        MISC_IN                => (others => '0'),
        MISC_OUT               => open
    );

    -- QSFP MAPPING ------------------------------------------------------------
    eth_refclk_p <= QSFP_REFCLK_156M & QSFP_REFCLK_156M; 
    eth_refclk_n <= (others => '0'); -- Quartus will handle the connection itself

    eth_rx_p <= QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP1_RX_N & QSFP0_RX_N;

    QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);

    -- BMC controller (ported from OFS) ----------------------------------------
    pmci_i : entity work.PMCI_TOP
    generic map(
        DEVICE => "AGILEX"
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

        QSPI_DCLK                => QSPI_DCLK,
        QSPI_NCS                 => QSPI_NCS,
        QSPI_DATA                => QSPI_DATA,
        NCSI_RBT_NCSI_CLK        => NCSI_RBT_NCSI_CLK,
        NCSI_RBT_NCSI_TXD        => NCSI_RBT_NCSI_TXD,
        NCSI_RBT_NCSI_TX_EN      => NCSI_RBT_NCSI_TX_EN,
        NCSI_RBT_NCSI_RXD        => NCSI_RBT_NCSI_RXD,
        NCSI_RBT_NCSI_CRS_DV     => NCSI_RBT_NCSI_CRS_DV,
        NCSI_RBT_NCSI_ARB_IN     => NCSI_RBT_NCSI_ARB_IN,
        NCSI_RBT_NCSI_ARB_OUT    => NCSI_RBT_NCSI_ARB_OUT,
        M10_GPIO_FPGA_USR_100M   => M10_GPIO_FPGA_USR_100M,
        M10_GPIO_FPGA_M10_HB     => M10_GPIO_FPGA_M10_HB,
        M10_GPIO_M10_SEU_ERROR   => M10_GPIO_M10_SEU_ERROR,
        M10_GPIO_FPGA_THERM_SHDN => M10_GPIO_FPGA_THERM_SHDN,
        M10_GPIO_FPGA_SEU_ERROR  => M10_GPIO_FPGA_SEU_ERROR,
        SPI_INGRESS_SCLK         => SPI_INGRESS_SCLK,
        SPI_INGRESS_CSN          => SPI_INGRESS_CSN,
        SPI_INGRESS_MISO         => SPI_INGRESS_MISO,
        SPI_INGRESS_MOSI         => SPI_INGRESS_MOSI,
        SPI_EGRESS_MOSI          => SPI_EGRESS_MOSI,
        SPI_EGRESS_CSN           => SPI_EGRESS_CSN,
        SPI_EGRESS_SCLK          => SPI_EGRESS_SCLK,
        SPI_EGRESS_MISO          => SPI_EGRESS_MISO
    );

    -- DDR4 EMIFs --------------------------------------------------------------

    ddr4_g: if (MEM_PORTS > 0) generate
        ddr4_ch0_i : component onboard_ddr4
        port map (
            local_reset_req      => emif_rst_req(0),
            local_reset_done     => emif_rst_done(0),
            pll_ref_clk          => DDR4_CH0_REF_CLK,
            pll_locked           => mem_pll_locked(0),
            oct_rzqin            => DDR4_CH0_OCT_RZQIN,
            mem_ck(0)            => DDR4_CH0_CK,
            mem_ck_n(0)          => DDR4_CH0_CK_N,
            mem_a                => DDR4_CH0_A,
            mem_act_n(0)         => DDR4_CH0_ACT_N,
            mem_ba               => DDR4_CH0_BA,
            mem_bg(0)            => DDR4_CH0_BG,
            mem_cke(0)           => DDR4_CH0_CKE,
            mem_cs_n             => DDR4_CH0_CS_N,
            mem_odt(0)           => DDR4_CH0_ODT,
            mem_reset_n(0)       => DDR4_CH0_RESET_N,
            mem_par(0)           => DDR4_CH0_PAR,
            mem_alert_n(0)       => DDR4_CH0_ALERT_N,
            mem_dqs              => DDR4_CH0_DQS,
            mem_dqs_n            => DDR4_CH0_DQS_N,
            mem_dq               => DDR4_CH0_DQ,
            mem_dbi_n            => DDR4_CH0_DBI_N,
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
            amm_readdatavalid_0  => mem_avmm_readdatavalid(0),
            calbus_read          => calbus_read(0),
            calbus_write         => calbus_write(0),
            calbus_address       => calbus_address(0),
            calbus_wdata         => calbus_wdata(0),
            calbus_rdata         => calbus_rdata(0),
            calbus_seq_param_tbl => calbus_seq_param_tbl(0),
            calbus_clk           => calbus_clk(0)
        );

        ddr4_ch1_i : component onboard_ddr4
        port map (
            local_reset_req      => emif_rst_req(1),
            local_reset_done     => emif_rst_done(1),
            pll_ref_clk          => DDR4_CH1_REF_CLK,
            pll_locked           => mem_pll_locked(1),
            oct_rzqin            => DDR4_CH1_OCT_RZQIN,
            mem_ck(0)            => DDR4_CH1_CK,
            mem_ck_n(0)          => DDR4_CH1_CK_N,
            mem_a                => DDR4_CH1_A,
            mem_act_n(0)         => DDR4_CH1_ACT_N,
            mem_ba               => DDR4_CH1_BA,
            mem_bg(0)            => DDR4_CH1_BG,
            mem_cke(0)           => DDR4_CH1_CKE,
            mem_cs_n             => DDR4_CH1_CS_N,
            mem_odt(0)           => DDR4_CH1_ODT,
            mem_reset_n(0)       => DDR4_CH1_RESET_N,
            mem_par(0)           => DDR4_CH1_PAR,
            mem_alert_n(0)       => DDR4_CH1_ALERT_N,
            mem_dqs              => DDR4_CH1_DQS,
            mem_dqs_n            => DDR4_CH1_DQS_N,
            mem_dq               => DDR4_CH1_DQ,
            mem_dbi_n            => DDR4_CH1_DBI_N,
            local_cal_success    => emif_cal_success(1),
            local_cal_fail       => emif_cal_fail(1),
            emif_usr_reset_n     => mem_rst_n(1),
            emif_usr_clk         => mem_clk(1),
            amm_ready_0          => mem_avmm_ready(1),
            amm_read_0           => mem_avmm_read(1),
            amm_write_0          => mem_avmm_write(1),
            amm_address_0        => mem_avmm_address(1),
            amm_readdata_0       => mem_avmm_readdata(1),
            amm_writedata_0      => mem_avmm_writedata(1),
            amm_burstcount_0     => mem_avmm_burstcount(1),
            amm_readdatavalid_0  => mem_avmm_readdatavalid(1),
            calbus_read          => calbus_read(1),
            calbus_write         => calbus_write(1),
            calbus_address       => calbus_address(1),
            calbus_wdata         => calbus_wdata(1),
            calbus_rdata         => calbus_rdata(1),
            calbus_seq_param_tbl => calbus_seq_param_tbl(1),
            calbus_clk           => calbus_clk(1)
        );

        ddr4_ch2_i : component onboard_ddr4
        port map (
            local_reset_req      => emif_rst_req(2),
            local_reset_done     => emif_rst_done(2),
            pll_ref_clk          => DDR4_CH2_REF_CLK,
            pll_locked           => mem_pll_locked(2),
            oct_rzqin            => DDR4_CH2_OCT_RZQIN,
            mem_ck(0)            => DDR4_CH2_CK,
            mem_ck_n(0)          => DDR4_CH2_CK_N,
            mem_a                => DDR4_CH2_A,
            mem_act_n(0)         => DDR4_CH2_ACT_N,
            mem_ba               => DDR4_CH2_BA,
            mem_bg(0)            => DDR4_CH2_BG,
            mem_cke(0)           => DDR4_CH2_CKE,
            mem_cs_n             => DDR4_CH2_CS_N,
            mem_odt(0)           => DDR4_CH2_ODT,
            mem_reset_n(0)       => DDR4_CH2_RESET_N,
            mem_par(0)           => DDR4_CH2_PAR,
            mem_alert_n(0)       => DDR4_CH2_ALERT_N,
            mem_dqs              => DDR4_CH2_DQS,
            mem_dqs_n            => DDR4_CH2_DQS_N,
            mem_dq               => DDR4_CH2_DQ,
            mem_dbi_n            => DDR4_CH2_DBI_N,
            local_cal_success    => emif_cal_success(2),
            local_cal_fail       => emif_cal_fail(2),
            emif_usr_reset_n     => mem_rst_n(2),
            emif_usr_clk         => mem_clk(2),
            amm_ready_0          => mem_avmm_ready(2),
            amm_read_0           => mem_avmm_read(2),
            amm_write_0          => mem_avmm_write(2),
            amm_address_0        => mem_avmm_address(2),
            amm_readdata_0       => mem_avmm_readdata(2),
            amm_writedata_0      => mem_avmm_writedata(2),
            amm_burstcount_0     => mem_avmm_burstcount(2),
            amm_readdatavalid_0  => mem_avmm_readdatavalid(2),
            calbus_read          => calbus_read(2),
            calbus_write         => calbus_write(2),
            calbus_address       => calbus_address(2),
            calbus_wdata         => calbus_wdata(2),
            calbus_rdata         => calbus_rdata(2),
            calbus_seq_param_tbl => calbus_seq_param_tbl(2),
            calbus_clk           => calbus_clk(2)
        );

        ddr4_ch3_i : component onboard_ddr4
        port map (
            local_reset_req      => emif_rst_req(3),
            local_reset_done     => emif_rst_done(3),
            pll_ref_clk          => DDR4_CH3_REF_CLK,
            pll_locked           => mem_pll_locked(3),
            oct_rzqin            => DDR4_CH3_OCT_RZQIN,
            mem_ck(0)            => DDR4_CH3_CK,
            mem_ck_n(0)          => DDR4_CH3_CK_N,
            mem_a                => DDR4_CH3_A,
            mem_act_n(0)         => DDR4_CH3_ACT_N,
            mem_ba               => DDR4_CH3_BA,
            mem_bg(0)            => DDR4_CH3_BG,
            mem_cke(0)           => DDR4_CH3_CKE,
            mem_cs_n             => DDR4_CH3_CS_N,
            mem_odt(0)           => DDR4_CH3_ODT,
            mem_reset_n(0)       => DDR4_CH3_RESET_N,
            mem_par(0)           => DDR4_CH3_PAR,
            mem_alert_n(0)       => DDR4_CH3_ALERT_N,
            mem_dqs              => DDR4_CH3_DQS,
            mem_dqs_n            => DDR4_CH3_DQS_N,
            mem_dq               => DDR4_CH3_DQ,
            mem_dbi_n            => DDR4_CH3_DBI_N,
            local_cal_success    => emif_cal_success(3),
            local_cal_fail       => emif_cal_fail(3),
            emif_usr_reset_n     => mem_rst_n(3),
            emif_usr_clk         => mem_clk(3),
            amm_ready_0          => mem_avmm_ready(3),
            amm_read_0           => mem_avmm_read(3),
            amm_write_0          => mem_avmm_write(3),
            amm_address_0        => mem_avmm_address(3),
            amm_readdata_0       => mem_avmm_readdata(3),
            amm_writedata_0      => mem_avmm_writedata(3),
            amm_burstcount_0     => mem_avmm_burstcount(3),
            amm_readdatavalid_0  => mem_avmm_readdatavalid(3),
            calbus_read          => calbus_read(3),
            calbus_write         => calbus_write(3),
            calbus_address       => calbus_address(3),
            calbus_wdata         => calbus_wdata(3),
            calbus_rdata         => calbus_rdata(3),
            calbus_seq_param_tbl => calbus_seq_param_tbl(3),
            calbus_clk           => calbus_clk(3)
        );

        ddr4_cal0_i : component ddr4_calibration
        port map (
            calbus_read_0          => calbus_read(0),              
            calbus_write_0         => calbus_write(0),       
            calbus_address_0       => calbus_address(0),     
            calbus_wdata_0         => calbus_wdata(0),    
            calbus_rdata_0         => calbus_rdata(0),       
            calbus_seq_param_tbl_0 => calbus_seq_param_tbl(0),
            calbus_read_1          => calbus_read(1),              
            calbus_write_1         => calbus_write(1),       
            calbus_address_1       => calbus_address(1),     
            calbus_wdata_1         => calbus_wdata(1),    
            calbus_rdata_1         => calbus_rdata(1),       
            calbus_seq_param_tbl_1 => calbus_seq_param_tbl(1),
            calbus_clk             => calbus_clk(0)
        );

        calbus_clk(1) <= calbus_clk(0);

        ddr4_cal1_i : component ddr4_calibration
        port map (
            calbus_read_0          => calbus_read(2),              
            calbus_write_0         => calbus_write(2),       
            calbus_address_0       => calbus_address(2),     
            calbus_wdata_0         => calbus_wdata(2),    
            calbus_rdata_0         => calbus_rdata(2),       
            calbus_seq_param_tbl_0 => calbus_seq_param_tbl(2),
            calbus_read_1          => calbus_read(3),              
            calbus_write_1         => calbus_write(3),       
            calbus_address_1       => calbus_address(3),     
            calbus_wdata_1         => calbus_wdata(3),    
            calbus_rdata_1         => calbus_rdata(3),       
            calbus_seq_param_tbl_1 => calbus_seq_param_tbl(3),
            calbus_clk             => calbus_clk(2)
        );

        calbus_clk(3) <= calbus_clk(2);
    else generate
        DDR4_CH0_BG      <= 'Z';
        DDR4_CH0_BA      <= (others => 'Z');
        DDR4_CH0_A       <= (others => 'Z');
        DDR4_CH0_PAR     <= 'Z';
        DDR4_CH0_CK_N    <= 'Z';
        DDR4_CH0_CK      <= 'Z';
        DDR4_CH0_CKE     <= 'Z';
        DDR4_CH0_ODT     <= 'Z';
        DDR4_CH0_ACT_N   <= 'Z';
        DDR4_CH0_CS_N    <= (others => 'Z');
        DDR4_CH0_RESET_N <= 'Z';
        DDR4_CH0_DQS     <= (others => 'Z');
        DDR4_CH0_DQS_N   <= (others => 'Z');
        DDR4_CH0_DQ      <= (others => 'Z');
        DDR4_CH0_DBI_N   <= (others => 'Z');

        DDR4_CH1_BG      <= 'Z';
        DDR4_CH1_BA      <= (others => 'Z');
        DDR4_CH1_A       <= (others => 'Z');
        DDR4_CH1_PAR     <= 'Z';
        DDR4_CH1_CK_N    <= 'Z';
        DDR4_CH1_CK      <= 'Z';
        DDR4_CH1_CKE     <= 'Z';
        DDR4_CH1_ODT     <= 'Z';
        DDR4_CH1_ACT_N   <= 'Z';
        DDR4_CH1_CS_N    <= (others => 'Z');
        DDR4_CH1_RESET_N <= 'Z';
        DDR4_CH1_DQS     <= (others => 'Z');
        DDR4_CH1_DQS_N   <= (others => 'Z');
        DDR4_CH1_DQ      <= (others => 'Z');
        DDR4_CH1_DBI_N   <= (others => 'Z');

        DDR4_CH2_BG      <= 'Z';
        DDR4_CH2_BA      <= (others => 'Z');
        DDR4_CH2_A       <= (others => 'Z');
        DDR4_CH2_PAR     <= 'Z';
        DDR4_CH2_CK_N    <= 'Z';
        DDR4_CH2_CK      <= 'Z';
        DDR4_CH2_CKE     <= 'Z';
        DDR4_CH2_ODT     <= 'Z';
        DDR4_CH2_ACT_N   <= 'Z';
        DDR4_CH2_CS_N    <= (others => 'Z');
        DDR4_CH2_RESET_N <= 'Z';
        DDR4_CH2_DQS     <= (others => 'Z');
        DDR4_CH2_DQS_N   <= (others => 'Z');
        DDR4_CH2_DQ      <= (others => 'Z');
        DDR4_CH2_DBI_N   <= (others => 'Z');

        DDR4_CH3_BG      <= 'Z';
        DDR4_CH3_BA      <= (others => 'Z');
        DDR4_CH3_A       <= (others => 'Z');
        DDR4_CH3_PAR     <= 'Z';
        DDR4_CH3_CK_N    <= 'Z';
        DDR4_CH3_CK      <= 'Z';
        DDR4_CH3_CKE     <= 'Z';
        DDR4_CH3_ODT     <= 'Z';
        DDR4_CH3_ACT_N   <= 'Z';
        DDR4_CH3_CS_N    <= (others => 'Z');
        DDR4_CH3_RESET_N <= 'Z';
        DDR4_CH3_DQS     <= (others => 'Z');
        DDR4_CH3_DQS_N   <= (others => 'Z');
        DDR4_CH3_DQ      <= (others => 'Z');
        DDR4_CH3_DBI_N   <= (others => 'Z');
    end generate;

end architecture;
