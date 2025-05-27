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
    -- DDR4
    -- =========================================================================
    DDR4_P0_REF_CLK   : in    std_logic;
    DDR4_P0_OCT_RZQIN : in    std_logic;
    DDR4_P0_ALERT_N   : in    std_logic;
    DDR4_P0_BG        : out   std_logic_vector(1-1 downto 0);
    DDR4_P0_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_P0_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_P0_PAR       : out   std_logic;
    DDR4_P0_CK_N      : out   std_logic;
    DDR4_P0_CK        : out   std_logic;
    DDR4_P0_CKE       : out   std_logic;
    DDR4_P0_ODT       : out   std_logic;
    DDR4_P0_ACT_N     : out   std_logic;
    DDR4_P0_CS_N      : out   std_logic_vector(1-1 downto 0);
    DDR4_P0_RESET_N   : out   std_logic;
    DDR4_P0_DQS_P     : inout std_logic_vector(9-1 downto 0);
    DDR4_P0_DQS_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_P0_DQ        : inout std_logic_vector(72-1 downto 0);
    DDR4_P0_DBI_N     : inout std_logic_vector(9-1 downto 0);

    DDR4_P1_REF_CLK   : in    std_logic;
    DDR4_P1_OCT_RZQIN : in    std_logic;
    DDR4_P1_ALERT_N   : in    std_logic;
    DDR4_P1_BG        : out   std_logic_vector(1-1 downto 0);
    DDR4_P1_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_P1_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_P1_PAR       : out   std_logic;
    DDR4_P1_CK_N      : out   std_logic;
    DDR4_P1_CK        : out   std_logic;
    DDR4_P1_CKE       : out   std_logic;
    DDR4_P1_ODT       : out   std_logic;
    DDR4_P1_ACT_N     : out   std_logic;
    DDR4_P1_CS_N      : out   std_logic_vector(1-1 downto 0);
    DDR4_P1_RESET_N   : out   std_logic;
    DDR4_P1_DQS_P     : inout std_logic_vector(9-1 downto 0);
    DDR4_P1_DQS_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_P1_DQ        : inout std_logic_vector(72-1 downto 0);
    DDR4_P1_DBI_N     : inout std_logic_vector(9-1 downto 0);

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

    component ddr4_calibration is
    port (
        calbus_read_0          : out std_logic;                                          -- calbus_read
        calbus_write_0         : out std_logic;                                          -- calbus_write
        calbus_address_0       : out std_logic_vector(19 downto 0);                      -- calbus_address
        calbus_wdata_0         : out std_logic_vector(31 downto 0);                      -- calbus_wdata
        calbus_rdata_0         : in  std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_rdata
        calbus_seq_param_tbl_0 : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl
        calbus_clk             : out std_logic                                           -- clk
    );
    end component;

    component onboard_ddr4_0 is
    port (
        local_reset_req      : in    std_logic                       := 'X';             -- local_reset_req
        local_reset_done     : out   std_logic;                                          -- local_reset_done
        pll_ref_clk          : in    std_logic                       := 'X';             -- clk
        pll_ref_clk_out      : out   std_logic;                                          -- clk
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
        mem_dqs              : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n            : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq               : inout std_logic_vector(71 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n            : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success    : out   std_logic;                                          -- local_cal_success
        local_cal_fail       : out   std_logic;                                          -- local_cal_fail
        emif_usr_reset_n     : out   std_logic;                                          -- reset_n
        emif_usr_clk         : out   std_logic;                                          -- clk
        amm_ready_0          : out   std_logic;                                          -- waitrequest_n
        amm_read_0           : in    std_logic                       := 'X';             -- read
        amm_write_0          : in    std_logic                       := 'X';             -- write
        amm_address_0        : in    std_logic_vector(26 downto 0)   := (others => 'X'); -- address
        amm_readdata_0       : out   std_logic_vector(575 downto 0);                     -- readdata
        amm_writedata_0      : in    std_logic_vector(575 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0     : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_byteenable_0     : in    std_logic_vector(71 downto 0)   := (others => 'X'); -- byteenable
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

    component onboard_ddr4_1 is
    port (
        local_reset_req           : in    std_logic                       := 'X';             -- local_reset_req
        local_reset_done          : out   std_logic;                                          -- local_reset_done
        pll_ref_clk               : in    std_logic                       := 'X';             -- clk
        pll_ref_clk_out           : out   std_logic;                                          -- clk
        pll_locked                : out   std_logic;                                          -- pll_locked
        oct_rzqin                 : in    std_logic                       := 'X';             -- oct_rzqin
        mem_ck                    : out   std_logic_vector(0 downto 0);                       -- mem_ck
        mem_ck_n                  : out   std_logic_vector(0 downto 0);                       -- mem_ck_n
        mem_a                     : out   std_logic_vector(16 downto 0);                      -- mem_a
        mem_act_n                 : out   std_logic_vector(0 downto 0);                       -- mem_act_n
        mem_ba                    : out   std_logic_vector(1 downto 0);                       -- mem_ba
        mem_bg                    : out   std_logic_vector(0 downto 0);                       -- mem_bg
        mem_cke                   : out   std_logic_vector(0 downto 0);                       -- mem_cke
        mem_cs_n                  : out   std_logic_vector(0 downto 0);                       -- mem_cs_n
        mem_odt                   : out   std_logic_vector(0 downto 0);                       -- mem_odt
        mem_reset_n               : out   std_logic_vector(0 downto 0);                       -- mem_reset_n
        mem_par                   : out   std_logic_vector(0 downto 0);                       -- mem_par
        mem_alert_n               : in    std_logic_vector(0 downto 0)    := (others => 'X'); -- mem_alert_n
        mem_dqs                   : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n                 : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq                    : inout std_logic_vector(71 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n                 : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success         : out   std_logic;                                          -- local_cal_success
        local_cal_fail            : out   std_logic;                                          -- local_cal_fail
        calbus_read               : in    std_logic                       := 'X';             -- calbus_read
        calbus_write              : in    std_logic                       := 'X';             -- calbus_write
        calbus_address            : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
        calbus_wdata              : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
        calbus_rdata              : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
        calbus_seq_param_tbl      : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
        calbus_clk                : in    std_logic                       := 'X';             -- clk
        emif_usr_reset_n          : out   std_logic;                                          -- reset_n
        emif_usr_clk              : out   std_logic;                                          -- clk
        ctrl_ecc_user_interrupt_0 : out   std_logic;                                          -- ctrl_ecc_user_interrupt
        amm_ready_0               : out   std_logic;                                          -- waitrequest_n
        amm_read_0                : in    std_logic                       := 'X';             -- read
        amm_write_0               : in    std_logic                       := 'X';             -- write
        amm_address_0             : in    std_logic_vector(26 downto 0)   := (others => 'X'); -- address
        amm_readdata_0            : out   std_logic_vector(511 downto 0);                     -- readdata
        amm_writedata_0           : in    std_logic_vector(511 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_byteenable_0          : in    std_logic_vector(63 downto 0)   := (others => 'X'); -- byteenable
        amm_readdatavalid_0       : out   std_logic                                           -- readdatavalid
    );
    end component;

    constant PCIE_LANES      : natural := 16;
    constant PCIE_CLKS       : natural := 2;
    constant PCIE_CONS       : natural := 1;
    constant MISC_IN_WIDTH   : natural := 4;
    constant MISC_OUT_WIDTH  : natural := 4;
    constant ETH_LANES       : natural := 8;
    constant DMA_ENDPOINTS   : natural := tsel(DMA_TYPE=3, 4, 1); -- 400G DMA Medusa = 4x DMA_ENDPOINT
    constant STATUS_LEDS     : natural := 2; -- fake, this board has only 1 status LED

    constant MEM_ADDR_WIDTH  : natural := 27;
    constant MEM_DATA_WIDTH  : natural := 512;
    constant MEM_BURST_WIDTH : natural := 7;
    constant AMM_FREQ_KHZ    : natural := 400000;

    constant QSFP_PORTS      : natural := 1;
    constant DEVICE          : string := "AGILEX";

    constant bmc_mi_addr_base : slv_array_t(2-1 downto 0)(32-1 downto 0) := (X"00000100", X"00000000");

    signal status_led_g      : std_logic_vector(STATUS_LEDS-1 downto 0);
    signal status_led_r      : std_logic_vector(STATUS_LEDS-1 downto 0);

    signal bmc_mi_clk        : std_logic;
    signal bmc_mi_reset      : std_logic;

    signal bmc_mi_addr          : std_logic_vector(32-1 downto 0);
    signal bmc_mi_dwr           : std_logic_vector(32-1 downto 0);
    signal bmc_mi_be            : std_logic_vector(32/8-1 downto 0);
    signal bmc_mi_rd            : std_logic;
    signal bmc_mi_wr            : std_logic;
    signal bmc_mi_drd           : std_logic_vector(32-1 downto 0);
    signal bmc_mi_ardy          : std_logic;
    signal bmc_mi_drdy          : std_logic;

    signal axi_mi_addr          : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_dwr           : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_be            : slv_array_t (2-1 downto 0)(32/8-1 downto 0);
    signal axi_mi_rd            : std_logic_vector(2-1 downto 0);
    signal axi_mi_wr            : std_logic_vector(2-1 downto 0);
    signal axi_mi_drd           : slv_array_t (2-1 downto 0)(32-1 downto 0);
    signal axi_mi_ardy          : std_logic_vector(2-1 downto 0);
    signal axi_mi_drdy          : std_logic_vector(2-1 downto 0);

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
    signal mem_avmm_readdata_full : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH+64-1 downto 0);
    signal mem_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');

    signal emif_rst_req           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_ecc_usr_int       : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_cal_success       : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '0');
    signal emif_cal_fail          : std_logic_vector(MEM_PORTS-1 downto 0) := (others => '1');

    signal qsfp_modprs_n    : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_int_n       : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_reset_n     : std_logic_vector(QSFP_PORTS-1 downto 0);
    signal qsfp_lpmode      : std_logic_vector(QSFP_PORTS-1 downto 0);

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

        QSFP_PORTS              => QSFP_PORTS,
        QSFP_I2C_PORTS          => 1,
        QSFP_I2C_CTRL_EN        => false,

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

        BOARD                   => "IA-440I",
        DEVICE                  => DEVICE
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

        QSFP_MODPRS_N          => qsfp_modprs_n,
        QSFP_INT_N             => qsfp_int_n,
        QSFP_LPMODE            => qsfp_lpmode,
        QSFP_RESET_N           => qsfp_reset_n,

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
        CLK     => bmc_mi_clk,
        RESET   => bmc_mi_reset,

        RX_DWR  => bmc_mi_dwr,
        RX_ADDR => bmc_mi_addr,
        RX_BE   => bmc_mi_be,
        RX_RD   => bmc_mi_rd,
        RX_WR   => bmc_mi_wr,
        RX_ARDY => bmc_mi_ardy,
        RX_DRD  => bmc_mi_drd,
        RX_DRDY => bmc_mi_drdy,

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
            CLK         => bmc_mi_clk,
            RESET       => bmc_mi_reset,

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
        host0_aclk              => bmc_mi_clk,
        host0_areset            => bmc_mi_reset,
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
        host1_aclk              => bmc_mi_clk,
        host1_areset            => bmc_mi_reset,
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
        cap_rom_aclk              => bmc_mi_clk,
        cap_rom_areset            => bmc_mi_reset,
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
        spi_sys_clk             => bmc_mi_clk,
        spi_sys_reset           => bmc_mi_reset,
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
        telemetry_clk           => bmc_mi_clk,
        telemetry_reset         => bmc_mi_reset,

        qsfpdd0_rst_n           => qsfp_reset_n(0),
        qsfpdd0_lpmode          => qsfp_lpmode(0),
        qsfpdd0_int_n           => qsfp_int_n(0),
        qsfpdd0_present_n       => qsfp_modprs_n(0)
    );

    -- =========================================================================
    -- DRAM
    -- =========================================================================

    ddr4_g: if (MEM_PORTS = 2) generate
        ddr4_p0_i : component onboard_ddr4_0
        port map (
            local_reset_req      => emif_rst_req(0),
            local_reset_done     => emif_rst_done(0),
            pll_ref_clk          => DDR4_P0_REF_CLK,
            pll_ref_clk_out      => open,
            pll_locked           => mem_pll_locked(0),
            oct_rzqin            => DDR4_P0_OCT_RZQIN,
            mem_ck(0)            => DDR4_P0_CK,
            mem_ck_n(0)          => DDR4_P0_CK_N,
            mem_a                => DDR4_P0_A,
            mem_act_n(0)         => DDR4_P0_ACT_N,
            mem_ba               => DDR4_P0_BA,
            mem_bg               => DDR4_P0_BG,
            mem_cke(0)           => DDR4_P0_CKE,
            mem_cs_n             => DDR4_P0_CS_N,
            mem_odt(0)           => DDR4_P0_ODT,
            mem_reset_n(0)       => DDR4_P0_RESET_N,
            mem_par(0)           => DDR4_P0_PAR,
            mem_alert_n(0)       => DDR4_P0_ALERT_N,
            mem_dqs              => DDR4_P0_DQS_P,
            mem_dqs_n            => DDR4_P0_DQS_N,
            mem_dq               => DDR4_P0_DQ,
            mem_dbi_n            => DDR4_P0_DBI_N,
            local_cal_success    => emif_cal_success(0),
            local_cal_fail       => emif_cal_fail(0),
            emif_usr_reset_n     => mem_rst_n(0),
            emif_usr_clk         => mem_clk(0),
            amm_ready_0          => mem_avmm_ready(0),
            amm_read_0           => mem_avmm_read(0),
            amm_write_0          => mem_avmm_write(0),
            amm_address_0        => mem_avmm_address(0),
            amm_readdata_0       => mem_avmm_readdata_full(0),
            amm_writedata_0(MEM_DATA_WIDTH-1 downto 0)   => mem_avmm_writedata(0),
            amm_writedata_0(576-1 downto MEM_DATA_WIDTH) => (others => '0'),
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

        mem_avmm_readdata(0) <= mem_avmm_readdata_full(0)(MEM_DATA_WIDTH-1 downto 0);

        ddr4_cal_p0_i : component ddr4_calibration
        port map (
            calbus_read_0          => calbus_read(0),
            calbus_write_0         => calbus_write(0),
            calbus_address_0       => calbus_address(0),
            calbus_wdata_0         => calbus_wdata(0),
            calbus_rdata_0         => calbus_rdata(0),
            calbus_seq_param_tbl_0 => calbus_seq_param_tbl(0),
            calbus_clk             => calbus_clk(0)
        );

        ddr4_p1_i : component onboard_ddr4_1
        port map (
            local_reset_req      => emif_rst_req(1),
            local_reset_done     => emif_rst_done(1),
            pll_ref_clk          => DDR4_P1_REF_CLK,
            pll_ref_clk_out      => open,
            pll_locked           => mem_pll_locked(1),
            oct_rzqin            => DDR4_P1_OCT_RZQIN,
            mem_ck(0)            => DDR4_P1_CK,
            mem_ck_n(0)          => DDR4_P1_CK_N,
            mem_a                => DDR4_P1_A,
            mem_act_n(0)         => DDR4_P1_ACT_N,
            mem_ba               => DDR4_P1_BA,
            mem_bg               => DDR4_P1_BG,
            mem_cke(0)           => DDR4_P1_CKE,
            mem_cs_n             => DDR4_P1_CS_N,
            mem_odt(0)           => DDR4_P1_ODT,
            mem_reset_n(0)       => DDR4_P1_RESET_N,
            mem_par(0)           => DDR4_P1_PAR,
            mem_alert_n(0)       => DDR4_P1_ALERT_N,
            mem_dqs              => DDR4_P1_DQS_P,
            mem_dqs_n            => DDR4_P1_DQS_N,
            mem_dq               => DDR4_P1_DQ,
            mem_dbi_n            => DDR4_P1_DBI_N,
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
            amm_byteenable_0     => (others => '1'),
            amm_readdatavalid_0  => mem_avmm_readdatavalid(1),
            ctrl_ecc_user_interrupt_0 => open,
            calbus_read          => calbus_read(1),
            calbus_write         => calbus_write(1),
            calbus_address       => calbus_address(1),
            calbus_wdata         => calbus_wdata(1),
            calbus_rdata         => calbus_rdata(1),
            calbus_seq_param_tbl => calbus_seq_param_tbl(1),
            calbus_clk           => calbus_clk(1)
        );

        ddr4_cal_p1_i : component ddr4_calibration
        port map (
            calbus_read_0          => calbus_read(1),
            calbus_write_0         => calbus_write(1),
            calbus_address_0       => calbus_address(1),
            calbus_wdata_0         => calbus_wdata(1),
            calbus_rdata_0         => calbus_rdata(1),
            calbus_seq_param_tbl_0 => calbus_seq_param_tbl(1),
            calbus_clk             => calbus_clk(1)
        );

    else generate
        DDR4_P0_BG      <= (others => 'Z');
        DDR4_P0_BA      <= (others => 'Z');
        DDR4_P0_A       <= (others => 'Z');
        DDR4_P0_PAR     <= 'Z';
        DDR4_P0_CK_N    <= 'Z';
        DDR4_P0_CK      <= 'Z';
        DDR4_P0_CKE     <= 'Z';
        DDR4_P0_ODT     <= 'Z';
        DDR4_P0_ACT_N   <= 'Z';
        DDR4_P0_CS_N    <= (others => 'Z');
        DDR4_P0_RESET_N <= 'Z';
        DDR4_P0_DQS_P   <= (others => 'Z');
        DDR4_P0_DQS_N   <= (others => 'Z');
        DDR4_P0_DQ      <= (others => 'Z');
        DDR4_P0_DBI_N   <= (others => 'Z');

        DDR4_P1_BG      <= (others => 'Z');
        DDR4_P1_BA      <= (others => 'Z');
        DDR4_P1_A       <= (others => 'Z');
        DDR4_P1_PAR     <= 'Z';
        DDR4_P1_CK_N    <= 'Z';
        DDR4_P1_CK      <= 'Z';
        DDR4_P1_CKE     <= 'Z';
        DDR4_P1_ODT     <= 'Z';
        DDR4_P1_ACT_N   <= 'Z';
        DDR4_P1_CS_N    <= (others => 'Z');
        DDR4_P1_RESET_N <= 'Z';
        DDR4_P1_DQS_P   <= (others => 'Z');
        DDR4_P1_DQS_N   <= (others => 'Z');
        DDR4_P1_DQ      <= (others => 'Z');
        DDR4_P1_DBI_N   <= (others => 'Z');
    end generate;

end architecture;
