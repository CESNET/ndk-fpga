-- fpga.vhd: Alveo U55C board top level entity and architecture
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
library unisim;
library xpm;

use xpm.vcomponents.all;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.combo_const.all;
use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;

use unisim.vcomponents.all;

entity FPGA is
port (
    -- 100 MHz external clocks 
    SYSCLK2_P           : in    std_logic;
    SYSCLK2_N           : in    std_logic;
    SYSCLK3_P           : in    std_logic;
    SYSCLK3_N           : in    std_logic;

    -- Alveo Satellite Controller (requires Alveo Card Management Solution IP)
    --MSP_GPIO            : in    std_logic_vector(3 downto 0);
    --MSP_UART_RXD        : in    std_logic;
    --MSP_UART_TXD        : out   std_logic;

    -- PCIe
    PCIE_SYSCLK0_P      : in    std_logic;
    PCIE_SYSCLK0_N      : in    std_logic;

    PCIE_SYSCLK1_P      : in    std_logic;
    PCIE_SYSCLK1_N      : in    std_logic;

    PCIE_SYSRST_N       : in    std_logic;
    PCIE_RX_P           : in    std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_RX_N           : in    std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_TX_P           : out   std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_TX_N           : out   std_logic_vector(PCIE_LANES -1 downto 0);

    -- QSFP data
    QSFP0_REFCLK_P      : in    std_logic;
    QSFP0_REFCLK_N      : in    std_logic;
    QSFP0_RX_P          : in    std_logic_vector(3 downto 0);
    QSFP0_RX_N          : in    std_logic_vector(3 downto 0);
    QSFP0_TX_P          : out   std_logic_vector(3 downto 0);
    QSFP0_TX_N          : out   std_logic_vector(3 downto 0);

    QSFP1_REFCLK_P      : in    std_logic;
    QSFP1_REFCLK_N      : in    std_logic;
    QSFP1_RX_P          : in    std_logic_vector(3 downto 0);
    QSFP1_RX_N          : in    std_logic_vector(3 downto 0);
    QSFP1_TX_P          : out   std_logic_vector(3 downto 0);
    QSFP1_TX_N          : out   std_logic_vector(3 downto 0);

    -- QSFP leds (one bit per QSFP port)
    QSFP_ACT_LED_G      : out   std_logic_vector(1 downto 0);
    QSFP_STA_LED_G      : out   std_logic_vector(1 downto 0);
    QSFP_STA_LED_Y      : out   std_logic_vector(1 downto 0);

    -- HBM CATTRIP 
    HBM_CATTRIP         : out   std_logic
);
end entity;

architecture FULL of FPGA is

    constant PCIE_CLKS           : integer := tsel(PCIE_ENDPOINT_MODE = 1, 2, 1);
    constant PCIE_CONS           : integer := 1;
    constant MISC_IN_WIDTH       : integer := 4;
    constant MISC_OUT_WIDTH      : integer := 4;
    constant ETH_LANES           : integer := 4;
    constant DMA_MODULES         : integer := PCIE_ENDPOINTS;
    constant DMA_ENDPOINTS       : integer := PCIE_ENDPOINTS;
    constant ETH_LANE_MAP        : integer_vector(2*ETH_LANES-1 downto 0) := (3, 2, 1, 0, 3, 2, 1, 0);
    constant ETH_LANE_RXPOLARITY : std_logic_vector(2*ETH_LANES-1 downto 0) := "00000000";
    constant ETH_LANE_TXPOLARITY : std_logic_vector(2*ETH_LANES-1 downto 0) := "00000000";
    constant DEVICE              : string  := "ULTRASCALE";

    constant HBM_DATA_WIDTH  : natural := 256;
    constant HBM_ADDR_WIDTH  : natural := 34;
    constant HBM_BURST_WIDTH : natural := 2;
    constant HBM_ID_WIDTH    : natural := 6;
    constant HBM_LEN_WIDTH   : natural := 4;
    constant HBM_SIZE_WIDTH  : natural := 3;
    constant HBM_RESP_WIDTH  : natural := 2;
    
    signal sysclk_ibuf      : std_logic;
    signal sysclk_bufg      : std_logic;
    signal sysrst_cnt       : unsigned(4 downto 0) := (others => '0');
    signal sysrst           : std_logic := '1';

    signal pcie_ref_clk_p   : std_logic_vector(PCIE_CLKS-1 downto 0);
    signal pcie_ref_clk_n   : std_logic_vector(PCIE_CLKS-1 downto 0);
    
    signal eth_refclk_p     : std_logic_vector(2-1 downto 0);
    signal eth_refclk_n     : std_logic_vector(2-1 downto 0);
    signal eth_rx_p         : std_logic_vector(2*ETH_LANES-1 downto 0);
    signal eth_rx_n         : std_logic_vector(2*ETH_LANES-1 downto 0);
    signal eth_tx_p         : std_logic_vector(2*ETH_LANES-1 downto 0);
    signal eth_tx_n         : std_logic_vector(2*ETH_LANES-1 downto 0);

    signal qsfp_lpmode      : std_logic_vector(2-1 downto 0) := (others => '1');
    signal qsfp_reset_n     : std_logic_vector(2-1 downto 0) := (others => '0');
    signal qsfp_scl         : std_logic_vector(2-1 downto 0) := (others => 'Z');
    signal qsfp_sda         : std_logic_vector(2-1 downto 0) := (others => 'Z');
    signal qsfp_modprs_n    : std_logic_vector(2-1 downto 0);
    signal qsfp_int_n       : std_logic_vector(2-1 downto 0);

    signal boot_mi_clk      : std_logic;
    signal boot_mi_reset    : std_logic;
    signal boot_mi_addr     : std_logic_vector(32-1 downto 0);
    signal boot_mi_dwr      : std_logic_vector(32-1 downto 0);
    signal boot_mi_wr       : std_logic;
    signal boot_mi_rd       : std_logic;
    signal boot_mi_be       : std_logic_vector((32/8)-1 downto 0);
    signal boot_mi_ardy     : std_logic;
    signal boot_mi_drd      : std_logic_vector(32-1 downto 0);
    signal boot_mi_drdy     : std_logic;
    -- ICAPE3 Controller
    signal boot_reset       : std_logic;
    signal boot_clk         : std_logic;
    signal icap_avail       : std_logic;
    signal icap_csib        : std_logic;
    signal icap_rdwrb       : std_logic;
    signal icap_di          : std_logic_vector(32-1 downto 0);
    signal icap_do          : std_logic_vector(32-1 downto 0);
    -- AXI QSPI Flash Controller
    signal axi_spi_clk      : std_logic;
    signal axi_mi_addr_s    : std_logic_vector(8-1 downto 0);
    signal axi_mi_dwr_s     : std_logic_vector(32-1 downto 0);
    signal axi_mi_wr_s      : std_logic;
    signal axi_mi_rd_s      : std_logic;
    signal axi_mi_be_s      : std_logic_vector((32/8)-1 downto 0);
    signal axi_mi_ardy_s    : std_logic;
    signal axi_mi_drd_s     : std_logic_vector(32-1 downto 0);
    signal axi_mi_drdy_s    : std_logic;

    signal misc_in          : std_logic_vector(MISC_IN_WIDTH-1 downto 0) := (others => '0');
    signal misc_out         : std_logic_vector(MISC_OUT_WIDTH-1 downto 0);

    signal hbm_sysclk_ibuf    : std_logic;
    signal hbm_refclk         : std_logic;
    signal hbm_refclk_rst     : std_logic;
    signal hbm_mmcm_clkfb     : std_logic;
    signal hbm_mmcm_lock      : std_logic;
    signal hbm_mmcm_lock_n    : std_logic;
    signal hbm_axi_aclk       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_areset_n   : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_apb_clk        : std_logic;
    signal hbm_apb_reset_n    : std_logic;
    signal hbm_ready          : std_logic_vector(2-1 downto 0);
    signal hbm_ready_sync     : std_logic_vector(2-1 downto 0);
    signal hbm0_cattrip       : std_logic;
    signal hbm1_cattrip       : std_logic;
    signal hbm_clk_mmcm       : std_logic;

    signal hbm_clk              : std_logic;
    signal hbm_reset            : std_logic;
    signal hbm_init_done        : std_logic;
    signal hbm_axi_araddr       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_arburst      : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_arid         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_arlen        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_arsize       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_arvalid      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arready      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rdata        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_rdata_parity : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_rid          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_rlast        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rresp        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_rvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rready       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_awaddr       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_awburst      : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_awid         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_awlen        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_awsize       : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_awvalid      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_awready      : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wdata        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_wdata_parity : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_wlast        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wstrb        : slv_array_t(HBM_PORTS-1 downto 0)((HBM_DATA_WIDTH/8)-1 downto 0);
    signal hbm_axi_wvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wready       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bid          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_bresp        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_bvalid       : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bready       : std_logic_vector(HBM_PORTS-1 downto 0);

    attribute keep : string;
    attribute keep of hbm_axi_areset_n : signal is "true";

    component hbm_ip
    port (
        HBM_REF_CLK_0 : IN STD_LOGIC;
        HBM_REF_CLK_1 : IN STD_LOGIC;
        AXI_00_ACLK : IN STD_LOGIC;
        AXI_00_ARESET_N : IN STD_LOGIC;
        AXI_00_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_00_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_00_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_00_ARVALID : IN STD_LOGIC;
        AXI_00_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_00_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_00_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_00_AWVALID : IN STD_LOGIC;
        AXI_00_RREADY : IN STD_LOGIC;
        AXI_00_BREADY : IN STD_LOGIC;
        AXI_00_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_00_WLAST : IN STD_LOGIC;
        AXI_00_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_WVALID : IN STD_LOGIC;
        AXI_01_ACLK : IN STD_LOGIC;
        AXI_01_ARESET_N : IN STD_LOGIC;
        AXI_01_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_01_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_01_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_01_ARVALID : IN STD_LOGIC;
        AXI_01_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_01_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_01_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_01_AWVALID : IN STD_LOGIC;
        AXI_01_RREADY : IN STD_LOGIC;
        AXI_01_BREADY : IN STD_LOGIC;
        AXI_01_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_01_WLAST : IN STD_LOGIC;
        AXI_01_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_WVALID : IN STD_LOGIC;
        AXI_02_ACLK : IN STD_LOGIC;
        AXI_02_ARESET_N : IN STD_LOGIC;
        AXI_02_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_02_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_02_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_02_ARVALID : IN STD_LOGIC;
        AXI_02_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_02_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_02_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_02_AWVALID : IN STD_LOGIC;
        AXI_02_RREADY : IN STD_LOGIC;
        AXI_02_BREADY : IN STD_LOGIC;
        AXI_02_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_02_WLAST : IN STD_LOGIC;
        AXI_02_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_WVALID : IN STD_LOGIC;
        AXI_03_ACLK : IN STD_LOGIC;
        AXI_03_ARESET_N : IN STD_LOGIC;
        AXI_03_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_03_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_03_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_03_ARVALID : IN STD_LOGIC;
        AXI_03_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_03_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_03_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_03_AWVALID : IN STD_LOGIC;
        AXI_03_RREADY : IN STD_LOGIC;
        AXI_03_BREADY : IN STD_LOGIC;
        AXI_03_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_03_WLAST : IN STD_LOGIC;
        AXI_03_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_WVALID : IN STD_LOGIC;
        AXI_04_ACLK : IN STD_LOGIC;
        AXI_04_ARESET_N : IN STD_LOGIC;
        AXI_04_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_04_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_04_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_04_ARVALID : IN STD_LOGIC;
        AXI_04_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_04_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_04_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_04_AWVALID : IN STD_LOGIC;
        AXI_04_RREADY : IN STD_LOGIC;
        AXI_04_BREADY : IN STD_LOGIC;
        AXI_04_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_04_WLAST : IN STD_LOGIC;
        AXI_04_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_WVALID : IN STD_LOGIC;
        AXI_05_ACLK : IN STD_LOGIC;
        AXI_05_ARESET_N : IN STD_LOGIC;
        AXI_05_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_05_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_05_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_05_ARVALID : IN STD_LOGIC;
        AXI_05_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_05_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_05_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_05_AWVALID : IN STD_LOGIC;
        AXI_05_RREADY : IN STD_LOGIC;
        AXI_05_BREADY : IN STD_LOGIC;
        AXI_05_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_05_WLAST : IN STD_LOGIC;
        AXI_05_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_WVALID : IN STD_LOGIC;
        AXI_06_ACLK : IN STD_LOGIC;
        AXI_06_ARESET_N : IN STD_LOGIC;
        AXI_06_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_06_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_06_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_06_ARVALID : IN STD_LOGIC;
        AXI_06_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_06_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_06_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_06_AWVALID : IN STD_LOGIC;
        AXI_06_RREADY : IN STD_LOGIC;
        AXI_06_BREADY : IN STD_LOGIC;
        AXI_06_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_06_WLAST : IN STD_LOGIC;
        AXI_06_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_WVALID : IN STD_LOGIC;
        AXI_07_ACLK : IN STD_LOGIC;
        AXI_07_ARESET_N : IN STD_LOGIC;
        AXI_07_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_07_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_07_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_07_ARVALID : IN STD_LOGIC;
        AXI_07_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_07_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_07_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_07_AWVALID : IN STD_LOGIC;
        AXI_07_RREADY : IN STD_LOGIC;
        AXI_07_BREADY : IN STD_LOGIC;
        AXI_07_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_07_WLAST : IN STD_LOGIC;
        AXI_07_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_WVALID : IN STD_LOGIC;
        AXI_08_ACLK : IN STD_LOGIC;
        AXI_08_ARESET_N : IN STD_LOGIC;
        AXI_08_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_08_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_08_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_08_ARVALID : IN STD_LOGIC;
        AXI_08_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_08_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_08_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_08_AWVALID : IN STD_LOGIC;
        AXI_08_RREADY : IN STD_LOGIC;
        AXI_08_BREADY : IN STD_LOGIC;
        AXI_08_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_08_WLAST : IN STD_LOGIC;
        AXI_08_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_WVALID : IN STD_LOGIC;
        AXI_09_ACLK : IN STD_LOGIC;
        AXI_09_ARESET_N : IN STD_LOGIC;
        AXI_09_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_09_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_09_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_09_ARVALID : IN STD_LOGIC;
        AXI_09_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_09_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_09_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_09_AWVALID : IN STD_LOGIC;
        AXI_09_RREADY : IN STD_LOGIC;
        AXI_09_BREADY : IN STD_LOGIC;
        AXI_09_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_09_WLAST : IN STD_LOGIC;
        AXI_09_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_WVALID : IN STD_LOGIC;
        AXI_10_ACLK : IN STD_LOGIC;
        AXI_10_ARESET_N : IN STD_LOGIC;
        AXI_10_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_10_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_10_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_10_ARVALID : IN STD_LOGIC;
        AXI_10_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_10_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_10_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_10_AWVALID : IN STD_LOGIC;
        AXI_10_RREADY : IN STD_LOGIC;
        AXI_10_BREADY : IN STD_LOGIC;
        AXI_10_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_10_WLAST : IN STD_LOGIC;
        AXI_10_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_WVALID : IN STD_LOGIC;
        AXI_11_ACLK : IN STD_LOGIC;
        AXI_11_ARESET_N : IN STD_LOGIC;
        AXI_11_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_11_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_11_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_11_ARVALID : IN STD_LOGIC;
        AXI_11_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_11_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_11_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_11_AWVALID : IN STD_LOGIC;
        AXI_11_RREADY : IN STD_LOGIC;
        AXI_11_BREADY : IN STD_LOGIC;
        AXI_11_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_11_WLAST : IN STD_LOGIC;
        AXI_11_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_WVALID : IN STD_LOGIC;
        AXI_12_ACLK : IN STD_LOGIC;
        AXI_12_ARESET_N : IN STD_LOGIC;
        AXI_12_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_12_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_12_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_12_ARVALID : IN STD_LOGIC;
        AXI_12_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_12_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_12_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_12_AWVALID : IN STD_LOGIC;
        AXI_12_RREADY : IN STD_LOGIC;
        AXI_12_BREADY : IN STD_LOGIC;
        AXI_12_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_12_WLAST : IN STD_LOGIC;
        AXI_12_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_WVALID : IN STD_LOGIC;
        AXI_13_ACLK : IN STD_LOGIC;
        AXI_13_ARESET_N : IN STD_LOGIC;
        AXI_13_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_13_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_13_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_13_ARVALID : IN STD_LOGIC;
        AXI_13_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_13_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_13_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_13_AWVALID : IN STD_LOGIC;
        AXI_13_RREADY : IN STD_LOGIC;
        AXI_13_BREADY : IN STD_LOGIC;
        AXI_13_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_13_WLAST : IN STD_LOGIC;
        AXI_13_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_WVALID : IN STD_LOGIC;
        AXI_14_ACLK : IN STD_LOGIC;
        AXI_14_ARESET_N : IN STD_LOGIC;
        AXI_14_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_14_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_14_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_14_ARVALID : IN STD_LOGIC;
        AXI_14_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_14_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_14_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_14_AWVALID : IN STD_LOGIC;
        AXI_14_RREADY : IN STD_LOGIC;
        AXI_14_BREADY : IN STD_LOGIC;
        AXI_14_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_14_WLAST : IN STD_LOGIC;
        AXI_14_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_WVALID : IN STD_LOGIC;
        AXI_15_ACLK : IN STD_LOGIC;
        AXI_15_ARESET_N : IN STD_LOGIC;
        AXI_15_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_15_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_15_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_15_ARVALID : IN STD_LOGIC;
        AXI_15_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_15_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_15_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_15_AWVALID : IN STD_LOGIC;
        AXI_15_RREADY : IN STD_LOGIC;
        AXI_15_BREADY : IN STD_LOGIC;
        AXI_15_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_15_WLAST : IN STD_LOGIC;
        AXI_15_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_WVALID : IN STD_LOGIC;
        AXI_16_ACLK : IN STD_LOGIC;
        AXI_16_ARESET_N : IN STD_LOGIC;
        AXI_16_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_16_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_16_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_16_ARVALID : IN STD_LOGIC;
        AXI_16_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_16_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_16_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_16_AWVALID : IN STD_LOGIC;
        AXI_16_RREADY : IN STD_LOGIC;
        AXI_16_BREADY : IN STD_LOGIC;
        AXI_16_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_16_WLAST : IN STD_LOGIC;
        AXI_16_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_WVALID : IN STD_LOGIC;
        AXI_17_ACLK : IN STD_LOGIC;
        AXI_17_ARESET_N : IN STD_LOGIC;
        AXI_17_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_17_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_17_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_17_ARVALID : IN STD_LOGIC;
        AXI_17_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_17_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_17_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_17_AWVALID : IN STD_LOGIC;
        AXI_17_RREADY : IN STD_LOGIC;
        AXI_17_BREADY : IN STD_LOGIC;
        AXI_17_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_17_WLAST : IN STD_LOGIC;
        AXI_17_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_WVALID : IN STD_LOGIC;
        AXI_18_ACLK : IN STD_LOGIC;
        AXI_18_ARESET_N : IN STD_LOGIC;
        AXI_18_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_18_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_18_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_18_ARVALID : IN STD_LOGIC;
        AXI_18_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_18_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_18_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_18_AWVALID : IN STD_LOGIC;
        AXI_18_RREADY : IN STD_LOGIC;
        AXI_18_BREADY : IN STD_LOGIC;
        AXI_18_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_18_WLAST : IN STD_LOGIC;
        AXI_18_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_WVALID : IN STD_LOGIC;
        AXI_19_ACLK : IN STD_LOGIC;
        AXI_19_ARESET_N : IN STD_LOGIC;
        AXI_19_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_19_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_19_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_19_ARVALID : IN STD_LOGIC;
        AXI_19_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_19_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_19_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_19_AWVALID : IN STD_LOGIC;
        AXI_19_RREADY : IN STD_LOGIC;
        AXI_19_BREADY : IN STD_LOGIC;
        AXI_19_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_19_WLAST : IN STD_LOGIC;
        AXI_19_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_WVALID : IN STD_LOGIC;
        AXI_20_ACLK : IN STD_LOGIC;
        AXI_20_ARESET_N : IN STD_LOGIC;
        AXI_20_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_20_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_20_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_20_ARVALID : IN STD_LOGIC;
        AXI_20_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_20_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_20_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_20_AWVALID : IN STD_LOGIC;
        AXI_20_RREADY : IN STD_LOGIC;
        AXI_20_BREADY : IN STD_LOGIC;
        AXI_20_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_20_WLAST : IN STD_LOGIC;
        AXI_20_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_WVALID : IN STD_LOGIC;
        AXI_21_ACLK : IN STD_LOGIC;
        AXI_21_ARESET_N : IN STD_LOGIC;
        AXI_21_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_21_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_21_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_21_ARVALID : IN STD_LOGIC;
        AXI_21_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_21_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_21_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_21_AWVALID : IN STD_LOGIC;
        AXI_21_RREADY : IN STD_LOGIC;
        AXI_21_BREADY : IN STD_LOGIC;
        AXI_21_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_21_WLAST : IN STD_LOGIC;
        AXI_21_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_WVALID : IN STD_LOGIC;
        AXI_22_ACLK : IN STD_LOGIC;
        AXI_22_ARESET_N : IN STD_LOGIC;
        AXI_22_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_22_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_22_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_22_ARVALID : IN STD_LOGIC;
        AXI_22_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_22_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_22_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_22_AWVALID : IN STD_LOGIC;
        AXI_22_RREADY : IN STD_LOGIC;
        AXI_22_BREADY : IN STD_LOGIC;
        AXI_22_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_22_WLAST : IN STD_LOGIC;
        AXI_22_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_WVALID : IN STD_LOGIC;
        AXI_23_ACLK : IN STD_LOGIC;
        AXI_23_ARESET_N : IN STD_LOGIC;
        AXI_23_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_23_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_23_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_23_ARVALID : IN STD_LOGIC;
        AXI_23_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_23_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_23_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_23_AWVALID : IN STD_LOGIC;
        AXI_23_RREADY : IN STD_LOGIC;
        AXI_23_BREADY : IN STD_LOGIC;
        AXI_23_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_23_WLAST : IN STD_LOGIC;
        AXI_23_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_WVALID : IN STD_LOGIC;
        AXI_24_ACLK : IN STD_LOGIC;
        AXI_24_ARESET_N : IN STD_LOGIC;
        AXI_24_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_24_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_24_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_24_ARVALID : IN STD_LOGIC;
        AXI_24_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_24_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_24_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_24_AWVALID : IN STD_LOGIC;
        AXI_24_RREADY : IN STD_LOGIC;
        AXI_24_BREADY : IN STD_LOGIC;
        AXI_24_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_24_WLAST : IN STD_LOGIC;
        AXI_24_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_WVALID : IN STD_LOGIC;
        AXI_25_ACLK : IN STD_LOGIC;
        AXI_25_ARESET_N : IN STD_LOGIC;
        AXI_25_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_25_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_25_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_25_ARVALID : IN STD_LOGIC;
        AXI_25_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_25_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_25_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_25_AWVALID : IN STD_LOGIC;
        AXI_25_RREADY : IN STD_LOGIC;
        AXI_25_BREADY : IN STD_LOGIC;
        AXI_25_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_25_WLAST : IN STD_LOGIC;
        AXI_25_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_WVALID : IN STD_LOGIC;
        AXI_26_ACLK : IN STD_LOGIC;
        AXI_26_ARESET_N : IN STD_LOGIC;
        AXI_26_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_26_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_26_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_26_ARVALID : IN STD_LOGIC;
        AXI_26_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_26_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_26_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_26_AWVALID : IN STD_LOGIC;
        AXI_26_RREADY : IN STD_LOGIC;
        AXI_26_BREADY : IN STD_LOGIC;
        AXI_26_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_26_WLAST : IN STD_LOGIC;
        AXI_26_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_WVALID : IN STD_LOGIC;
        AXI_27_ACLK : IN STD_LOGIC;
        AXI_27_ARESET_N : IN STD_LOGIC;
        AXI_27_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_27_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_27_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_27_ARVALID : IN STD_LOGIC;
        AXI_27_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_27_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_27_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_27_AWVALID : IN STD_LOGIC;
        AXI_27_RREADY : IN STD_LOGIC;
        AXI_27_BREADY : IN STD_LOGIC;
        AXI_27_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_27_WLAST : IN STD_LOGIC;
        AXI_27_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_WVALID : IN STD_LOGIC;
        AXI_28_ACLK : IN STD_LOGIC;
        AXI_28_ARESET_N : IN STD_LOGIC;
        AXI_28_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_28_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_28_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_28_ARVALID : IN STD_LOGIC;
        AXI_28_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_28_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_28_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_28_AWVALID : IN STD_LOGIC;
        AXI_28_RREADY : IN STD_LOGIC;
        AXI_28_BREADY : IN STD_LOGIC;
        AXI_28_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_28_WLAST : IN STD_LOGIC;
        AXI_28_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_WVALID : IN STD_LOGIC;
        AXI_29_ACLK : IN STD_LOGIC;
        AXI_29_ARESET_N : IN STD_LOGIC;
        AXI_29_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_29_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_29_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_29_ARVALID : IN STD_LOGIC;
        AXI_29_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_29_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_29_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_29_AWVALID : IN STD_LOGIC;
        AXI_29_RREADY : IN STD_LOGIC;
        AXI_29_BREADY : IN STD_LOGIC;
        AXI_29_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_29_WLAST : IN STD_LOGIC;
        AXI_29_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_WVALID : IN STD_LOGIC;
        AXI_30_ACLK : IN STD_LOGIC;
        AXI_30_ARESET_N : IN STD_LOGIC;
        AXI_30_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_30_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_30_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_30_ARVALID : IN STD_LOGIC;
        AXI_30_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_30_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_30_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_30_AWVALID : IN STD_LOGIC;
        AXI_30_RREADY : IN STD_LOGIC;
        AXI_30_BREADY : IN STD_LOGIC;
        AXI_30_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_30_WLAST : IN STD_LOGIC;
        AXI_30_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_WVALID : IN STD_LOGIC;
        AXI_31_ACLK : IN STD_LOGIC;
        AXI_31_ARESET_N : IN STD_LOGIC;
        AXI_31_ARADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_31_ARBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_ARID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_ARLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_31_ARSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_31_ARVALID : IN STD_LOGIC;
        AXI_31_AWADDR : IN STD_LOGIC_VECTOR(33 DOWNTO 0);
        AXI_31_AWBURST : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_AWID : IN STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_AWLEN : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
        AXI_31_AWSIZE : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
        AXI_31_AWVALID : IN STD_LOGIC;
        AXI_31_RREADY : IN STD_LOGIC;
        AXI_31_BREADY : IN STD_LOGIC;
        AXI_31_WDATA : IN STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_31_WLAST : IN STD_LOGIC;
        AXI_31_WSTRB : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_WDATA_PARITY : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_WVALID : IN STD_LOGIC;
        APB_0_PCLK : IN STD_LOGIC;
        APB_0_PRESET_N : IN STD_LOGIC;
        APB_1_PCLK : IN STD_LOGIC;
        APB_1_PRESET_N : IN STD_LOGIC;
        AXI_00_ARREADY : OUT STD_LOGIC;
        AXI_00_AWREADY : OUT STD_LOGIC;
        AXI_00_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_00_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_00_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_RLAST : OUT STD_LOGIC;
        AXI_00_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_RVALID : OUT STD_LOGIC;
        AXI_00_WREADY : OUT STD_LOGIC;
        AXI_00_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_00_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_00_BVALID : OUT STD_LOGIC;
        AXI_01_ARREADY : OUT STD_LOGIC;
        AXI_01_AWREADY : OUT STD_LOGIC;
        AXI_01_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_01_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_01_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_RLAST : OUT STD_LOGIC;
        AXI_01_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_RVALID : OUT STD_LOGIC;
        AXI_01_WREADY : OUT STD_LOGIC;
        AXI_01_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_01_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_01_BVALID : OUT STD_LOGIC;
        AXI_02_ARREADY : OUT STD_LOGIC;
        AXI_02_AWREADY : OUT STD_LOGIC;
        AXI_02_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_02_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_02_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_RLAST : OUT STD_LOGIC;
        AXI_02_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_RVALID : OUT STD_LOGIC;
        AXI_02_WREADY : OUT STD_LOGIC;
        AXI_02_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_02_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_02_BVALID : OUT STD_LOGIC;
        AXI_03_ARREADY : OUT STD_LOGIC;
        AXI_03_AWREADY : OUT STD_LOGIC;
        AXI_03_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_03_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_03_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_RLAST : OUT STD_LOGIC;
        AXI_03_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_RVALID : OUT STD_LOGIC;
        AXI_03_WREADY : OUT STD_LOGIC;
        AXI_03_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_03_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_03_BVALID : OUT STD_LOGIC;
        AXI_04_ARREADY : OUT STD_LOGIC;
        AXI_04_AWREADY : OUT STD_LOGIC;
        AXI_04_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_04_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_04_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_RLAST : OUT STD_LOGIC;
        AXI_04_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_RVALID : OUT STD_LOGIC;
        AXI_04_WREADY : OUT STD_LOGIC;
        AXI_04_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_04_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_04_BVALID : OUT STD_LOGIC;
        AXI_05_ARREADY : OUT STD_LOGIC;
        AXI_05_AWREADY : OUT STD_LOGIC;
        AXI_05_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_05_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_05_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_RLAST : OUT STD_LOGIC;
        AXI_05_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_RVALID : OUT STD_LOGIC;
        AXI_05_WREADY : OUT STD_LOGIC;
        AXI_05_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_05_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_05_BVALID : OUT STD_LOGIC;
        AXI_06_ARREADY : OUT STD_LOGIC;
        AXI_06_AWREADY : OUT STD_LOGIC;
        AXI_06_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_06_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_06_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_RLAST : OUT STD_LOGIC;
        AXI_06_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_RVALID : OUT STD_LOGIC;
        AXI_06_WREADY : OUT STD_LOGIC;
        AXI_06_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_06_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_06_BVALID : OUT STD_LOGIC;
        AXI_07_ARREADY : OUT STD_LOGIC;
        AXI_07_AWREADY : OUT STD_LOGIC;
        AXI_07_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_07_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_07_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_RLAST : OUT STD_LOGIC;
        AXI_07_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_RVALID : OUT STD_LOGIC;
        AXI_07_WREADY : OUT STD_LOGIC;
        AXI_07_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_07_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_07_BVALID : OUT STD_LOGIC;
        AXI_08_ARREADY : OUT STD_LOGIC;
        AXI_08_AWREADY : OUT STD_LOGIC;
        AXI_08_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_08_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_08_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_RLAST : OUT STD_LOGIC;
        AXI_08_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_RVALID : OUT STD_LOGIC;
        AXI_08_WREADY : OUT STD_LOGIC;
        AXI_08_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_08_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_08_BVALID : OUT STD_LOGIC;
        AXI_09_ARREADY : OUT STD_LOGIC;
        AXI_09_AWREADY : OUT STD_LOGIC;
        AXI_09_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_09_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_09_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_RLAST : OUT STD_LOGIC;
        AXI_09_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_RVALID : OUT STD_LOGIC;
        AXI_09_WREADY : OUT STD_LOGIC;
        AXI_09_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_09_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_09_BVALID : OUT STD_LOGIC;
        AXI_10_ARREADY : OUT STD_LOGIC;
        AXI_10_AWREADY : OUT STD_LOGIC;
        AXI_10_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_10_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_10_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_RLAST : OUT STD_LOGIC;
        AXI_10_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_RVALID : OUT STD_LOGIC;
        AXI_10_WREADY : OUT STD_LOGIC;
        AXI_10_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_10_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_10_BVALID : OUT STD_LOGIC;
        AXI_11_ARREADY : OUT STD_LOGIC;
        AXI_11_AWREADY : OUT STD_LOGIC;
        AXI_11_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_11_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_11_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_RLAST : OUT STD_LOGIC;
        AXI_11_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_RVALID : OUT STD_LOGIC;
        AXI_11_WREADY : OUT STD_LOGIC;
        AXI_11_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_11_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_11_BVALID : OUT STD_LOGIC;
        AXI_12_ARREADY : OUT STD_LOGIC;
        AXI_12_AWREADY : OUT STD_LOGIC;
        AXI_12_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_12_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_12_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_RLAST : OUT STD_LOGIC;
        AXI_12_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_RVALID : OUT STD_LOGIC;
        AXI_12_WREADY : OUT STD_LOGIC;
        AXI_12_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_12_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_12_BVALID : OUT STD_LOGIC;
        AXI_13_ARREADY : OUT STD_LOGIC;
        AXI_13_AWREADY : OUT STD_LOGIC;
        AXI_13_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_13_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_13_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_RLAST : OUT STD_LOGIC;
        AXI_13_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_RVALID : OUT STD_LOGIC;
        AXI_13_WREADY : OUT STD_LOGIC;
        AXI_13_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_13_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_13_BVALID : OUT STD_LOGIC;
        AXI_14_ARREADY : OUT STD_LOGIC;
        AXI_14_AWREADY : OUT STD_LOGIC;
        AXI_14_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_14_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_14_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_RLAST : OUT STD_LOGIC;
        AXI_14_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_RVALID : OUT STD_LOGIC;
        AXI_14_WREADY : OUT STD_LOGIC;
        AXI_14_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_14_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_14_BVALID : OUT STD_LOGIC;
        AXI_15_ARREADY : OUT STD_LOGIC;
        AXI_15_AWREADY : OUT STD_LOGIC;
        AXI_15_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_15_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_15_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_RLAST : OUT STD_LOGIC;
        AXI_15_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_RVALID : OUT STD_LOGIC;
        AXI_15_WREADY : OUT STD_LOGIC;
        AXI_15_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_15_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_15_BVALID : OUT STD_LOGIC;
        AXI_16_ARREADY : OUT STD_LOGIC;
        AXI_16_AWREADY : OUT STD_LOGIC;
        AXI_16_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_16_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_16_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_RLAST : OUT STD_LOGIC;
        AXI_16_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_RVALID : OUT STD_LOGIC;
        AXI_16_WREADY : OUT STD_LOGIC;
        AXI_16_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_16_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_16_BVALID : OUT STD_LOGIC;
        AXI_17_ARREADY : OUT STD_LOGIC;
        AXI_17_AWREADY : OUT STD_LOGIC;
        AXI_17_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_17_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_17_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_RLAST : OUT STD_LOGIC;
        AXI_17_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_RVALID : OUT STD_LOGIC;
        AXI_17_WREADY : OUT STD_LOGIC;
        AXI_17_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_17_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_17_BVALID : OUT STD_LOGIC;
        AXI_18_ARREADY : OUT STD_LOGIC;
        AXI_18_AWREADY : OUT STD_LOGIC;
        AXI_18_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_18_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_18_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_RLAST : OUT STD_LOGIC;
        AXI_18_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_RVALID : OUT STD_LOGIC;
        AXI_18_WREADY : OUT STD_LOGIC;
        AXI_18_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_18_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_18_BVALID : OUT STD_LOGIC;
        AXI_19_ARREADY : OUT STD_LOGIC;
        AXI_19_AWREADY : OUT STD_LOGIC;
        AXI_19_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_19_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_19_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_RLAST : OUT STD_LOGIC;
        AXI_19_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_RVALID : OUT STD_LOGIC;
        AXI_19_WREADY : OUT STD_LOGIC;
        AXI_19_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_19_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_19_BVALID : OUT STD_LOGIC;
        AXI_20_ARREADY : OUT STD_LOGIC;
        AXI_20_AWREADY : OUT STD_LOGIC;
        AXI_20_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_20_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_20_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_RLAST : OUT STD_LOGIC;
        AXI_20_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_RVALID : OUT STD_LOGIC;
        AXI_20_WREADY : OUT STD_LOGIC;
        AXI_20_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_20_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_20_BVALID : OUT STD_LOGIC;
        AXI_21_ARREADY : OUT STD_LOGIC;
        AXI_21_AWREADY : OUT STD_LOGIC;
        AXI_21_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_21_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_21_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_RLAST : OUT STD_LOGIC;
        AXI_21_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_RVALID : OUT STD_LOGIC;
        AXI_21_WREADY : OUT STD_LOGIC;
        AXI_21_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_21_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_21_BVALID : OUT STD_LOGIC;
        AXI_22_ARREADY : OUT STD_LOGIC;
        AXI_22_AWREADY : OUT STD_LOGIC;
        AXI_22_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_22_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_22_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_RLAST : OUT STD_LOGIC;
        AXI_22_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_RVALID : OUT STD_LOGIC;
        AXI_22_WREADY : OUT STD_LOGIC;
        AXI_22_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_22_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_22_BVALID : OUT STD_LOGIC;
        AXI_23_ARREADY : OUT STD_LOGIC;
        AXI_23_AWREADY : OUT STD_LOGIC;
        AXI_23_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_23_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_23_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_RLAST : OUT STD_LOGIC;
        AXI_23_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_RVALID : OUT STD_LOGIC;
        AXI_23_WREADY : OUT STD_LOGIC;
        AXI_23_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_23_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_23_BVALID : OUT STD_LOGIC;
        AXI_24_ARREADY : OUT STD_LOGIC;
        AXI_24_AWREADY : OUT STD_LOGIC;
        AXI_24_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_24_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_24_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_RLAST : OUT STD_LOGIC;
        AXI_24_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_RVALID : OUT STD_LOGIC;
        AXI_24_WREADY : OUT STD_LOGIC;
        AXI_24_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_24_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_24_BVALID : OUT STD_LOGIC;
        AXI_25_ARREADY : OUT STD_LOGIC;
        AXI_25_AWREADY : OUT STD_LOGIC;
        AXI_25_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_25_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_25_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_RLAST : OUT STD_LOGIC;
        AXI_25_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_RVALID : OUT STD_LOGIC;
        AXI_25_WREADY : OUT STD_LOGIC;
        AXI_25_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_25_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_25_BVALID : OUT STD_LOGIC;
        AXI_26_ARREADY : OUT STD_LOGIC;
        AXI_26_AWREADY : OUT STD_LOGIC;
        AXI_26_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_26_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_26_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_RLAST : OUT STD_LOGIC;
        AXI_26_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_RVALID : OUT STD_LOGIC;
        AXI_26_WREADY : OUT STD_LOGIC;
        AXI_26_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_26_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_26_BVALID : OUT STD_LOGIC;
        AXI_27_ARREADY : OUT STD_LOGIC;
        AXI_27_AWREADY : OUT STD_LOGIC;
        AXI_27_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_27_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_27_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_RLAST : OUT STD_LOGIC;
        AXI_27_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_RVALID : OUT STD_LOGIC;
        AXI_27_WREADY : OUT STD_LOGIC;
        AXI_27_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_27_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_27_BVALID : OUT STD_LOGIC;
        AXI_28_ARREADY : OUT STD_LOGIC;
        AXI_28_AWREADY : OUT STD_LOGIC;
        AXI_28_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_28_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_28_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_RLAST : OUT STD_LOGIC;
        AXI_28_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_RVALID : OUT STD_LOGIC;
        AXI_28_WREADY : OUT STD_LOGIC;
        AXI_28_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_28_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_28_BVALID : OUT STD_LOGIC;
        AXI_29_ARREADY : OUT STD_LOGIC;
        AXI_29_AWREADY : OUT STD_LOGIC;
        AXI_29_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_29_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_29_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_RLAST : OUT STD_LOGIC;
        AXI_29_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_RVALID : OUT STD_LOGIC;
        AXI_29_WREADY : OUT STD_LOGIC;
        AXI_29_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_29_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_29_BVALID : OUT STD_LOGIC;
        AXI_30_ARREADY : OUT STD_LOGIC;
        AXI_30_AWREADY : OUT STD_LOGIC;
        AXI_30_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_30_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_30_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_RLAST : OUT STD_LOGIC;
        AXI_30_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_RVALID : OUT STD_LOGIC;
        AXI_30_WREADY : OUT STD_LOGIC;
        AXI_30_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_30_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_30_BVALID : OUT STD_LOGIC;
        AXI_31_ARREADY : OUT STD_LOGIC;
        AXI_31_AWREADY : OUT STD_LOGIC;
        AXI_31_RDATA_PARITY : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
        AXI_31_RDATA : OUT STD_LOGIC_VECTOR(255 DOWNTO 0);
        AXI_31_RID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_RLAST : OUT STD_LOGIC;
        AXI_31_RRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_RVALID : OUT STD_LOGIC;
        AXI_31_WREADY : OUT STD_LOGIC;
        AXI_31_BID : OUT STD_LOGIC_VECTOR(5 DOWNTO 0);
        AXI_31_BRESP : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
        AXI_31_BVALID : OUT STD_LOGIC;
        apb_complete_0 : OUT STD_LOGIC;
        apb_complete_1 : OUT STD_LOGIC;
        DRAM_0_STAT_CATTRIP : OUT STD_LOGIC;
        DRAM_0_STAT_TEMP : OUT STD_LOGIC_VECTOR(6 DOWNTO 0);
        DRAM_1_STAT_CATTRIP : OUT STD_LOGIC;
        DRAM_1_STAT_TEMP : OUT STD_LOGIC_VECTOR(6 DOWNTO 0) 
    );
end component;

begin

    sysclk_ibuf_i : IBUFDS
    port map (
        I  => SYSCLK2_P,
        IB => SYSCLK2_N,
        O  => sysclk_ibuf
    );

    sysclk_bufg_i : BUFG
    port map (
        I => sysclk_ibuf,
        O => sysclk_bufg
    );

    -- reset after power up
    process(sysclk_bufg)
    begin
        if rising_edge(sysclk_bufg) then
            if (sysrst_cnt(sysrst_cnt'high) = '0') then
                sysrst_cnt <= sysrst_cnt + 1;
            end if;
            sysrst <= not sysrst_cnt(sysrst_cnt'high);
        end if;
    end process;

    -- QSFP MAPPING ------------------------------------------------------------
    eth_refclk_p <= QSFP1_REFCLK_P & QSFP0_REFCLK_P; 
    eth_refclk_n <= QSFP1_REFCLK_N & QSFP0_REFCLK_N;

    eth_rx_p <= QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP1_RX_N & QSFP0_RX_N;

    net_arch_empty_g: if (NET_MOD_ARCH /= "EMPTY") generate
        QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
        QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);
        QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
        QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);
    end generate;

    QSFP_ACT_LED_G <= (others => '0');

    -- =========================================================================
    -- BOOT AND FLASH
    -- =========================================================================

    axi_spi_clk     <= misc_out(0); -- usr_x1 = 100MHz
    boot_clk        <= misc_out(2); -- usr_x2 = 200MHz
    boot_reset      <= misc_out(3);

    boot_ctrl_i : entity work.BOOT_CTRL
    generic map(
        ICAP_WBSTAR0 => X"01002000",
        ICAP_WBSTAR1 => X"01002000", --TODO
        DEVICE       => "ULTRASCALE",
        BOOT_TYPE    => 1
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

        BOOT_CLK      => boot_clk,
        BOOT_RESET    => boot_reset,

        BOOT_REQUEST  => open,
        BOOT_IMAGE    => open,

        ICAP_AVAIL    => icap_avail,
        ICAP_CSIB     => icap_csib,
        ICAP_RDWRB    => icap_rdwrb,
        ICAP_DI       => icap_di,
        ICAP_DO       => icap_do,

        BMC_MI_ADDR   => open,
        BMC_MI_DWR    => open,
        BMC_MI_WR     => open,
        BMC_MI_RD     => open,
        BMC_MI_BE     => open,
        BMC_MI_ARDY   => '0',
        BMC_MI_DRD    => (others => '0'),
        BMC_MI_DRDY   => '0',

        AXI_MI_ADDR   => axi_mi_addr_s,
        AXI_MI_DWR    => axi_mi_dwr_s,
        AXI_MI_WR     => axi_mi_wr_s,
        AXI_MI_RD     => axi_mi_rd_s,
        AXI_MI_BE     => axi_mi_be_s,
        AXI_MI_ARDY   => axi_mi_ardy_s,
        AXI_MI_DRD    => axi_mi_drd_s,
        AXI_MI_DRDY   => axi_mi_drdy_s
    );

    -- ICAPE3 CTRL
    icape3_i : ICAPE3
    generic map (
       DEVICE_ID         => X"76543210", -- only for SIM
       ICAP_AUTO_SWITCH  => "DISABLE",
       SIM_CFG_FILE_NAME => "NONE"
    )
    port map (
       AVAIL   => icap_avail,
       O       => icap_do,
       PRDONE  => open,
       PRERROR => open,
       CLK     => boot_clk,
       CSIB    => icap_csib,
       I       => icap_di,
       RDWRB   => icap_rdwrb
    );

    axi_qspi_flash_i: entity work.axi_quad_flash_controller
    port map(
        -- clock and reset
        SPI_CLK      => axi_spi_clk,
        CLK          => boot_clk,
        RST          => boot_reset,

        -- MI32 protocol
        AXI_MI_ADDR => axi_mi_addr_s,
        AXI_MI_DWR  => axi_mi_dwr_s,
        AXI_MI_WR   => axi_mi_wr_s,
        AXI_MI_RD   => axi_mi_rd_s,
        AXI_MI_BE   => axi_mi_be_s,
        AXI_MI_ARDY => axi_mi_ardy_s,
        AXI_MI_DRD  => axi_mi_drd_s,
        AXI_MI_DRDY => axi_mi_drdy_s,

        -- STARTUP I/O signals
        CFGCLK      => open,
        CFGMCLK     => open,
        EOS         => open,
        PREQ        => open
    );

    -- =========================================================================
    -- FPGA COMMON
    -- =========================================================================

    cm_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 10.0,
        PLL_MULT_F              => 12.0,
        PLL_MASTER_DIV          => 1,
        PLL_OUT0_DIV_F          => 3.0,
        PLL_OUT1_DIV            => 4,
        PLL_OUT2_DIV            => 6,
        PLL_OUT3_DIV            => 12,

        USE_PCIE_CLK            => False,
        
        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,
        PCIE_CONS               => PCIE_CONS,
        PCIE_ENDPOINTS          => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE      => PCIE_MOD_ARCH,
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,

        DMA_ENDPOINTS           => DMA_ENDPOINTS,
        DMA_MODULES             => DMA_MODULES,
        DMA_RX_CHANNELS         => DMA_RX_CHANNELS/DMA_MODULES,
        DMA_TX_CHANNELS         => DMA_TX_CHANNELS/DMA_MODULES,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_LANES               => ETH_LANES,
        ETH_LANE_MAP            => ETH_LANE_MAP(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_LANE_RXPOLARITY     => ETH_LANE_RXPOLARITY(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_LANE_TXPOLARITY     => ETH_LANE_TXPOLARITY(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_PORT_LEDS           => 1,
        QSFP_PORTS              => ETH_PORTS,
        QSFP_I2C_PORTS          => ETH_PORTS,

        HBM_PORTS               => HBM_PORTS,
        HBM_DATA_WIDTH          => HBM_DATA_WIDTH,
        HBM_ADDR_WIDTH          => HBM_ADDR_WIDTH,
        HBM_BURST_WIDTH         => HBM_BURST_WIDTH,
        HBM_ID_WIDTH            => HBM_ID_WIDTH,
        HBM_LEN_WIDTH           => HBM_LEN_WIDTH,
        HBM_SIZE_WIDTH          => HBM_SIZE_WIDTH,
        HBM_RESP_WIDTH          => HBM_RESP_WIDTH,

        MEM_PORTS               => MEM_PORTS, -- must be 0

        STATUS_LEDS             => 2, -- fake leds

        MISC_IN_WIDTH           => MISC_IN_WIDTH,
        MISC_OUT_WIDTH          => MISC_OUT_WIDTH,

        BOARD                   => CARD_NAME,
        DEVICE                  => DEVICE
    )
    port map(
        SYSCLK                  => sysclk_bufg,
        SYSRST                  => sysrst,

        PCIE_SYSCLK_P           => pcie_ref_clk_p,
        PCIE_SYSCLK_N           => pcie_ref_clk_n,
        PCIE_SYSRST_N(0)        => PCIE_SYSRST_N,
        PCIE_RX_P               => PCIE_RX_P,
        PCIE_RX_N               => PCIE_RX_N,
        PCIE_TX_P               => PCIE_TX_P,
        PCIE_TX_N               => PCIE_TX_N,

        ETH_REFCLK_P            => eth_refclk_p(ETH_PORTS-1 downto 0),
        ETH_REFCLK_N            => eth_refclk_n(ETH_PORTS-1 downto 0),

        ETH_RX_P                => eth_rx_p(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_RX_N                => eth_rx_n(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_TX_P                => eth_tx_p(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_TX_N                => eth_tx_n(ETH_PORTS*ETH_LANES-1 downto 0),

        ETH_LED_R               => QSFP_STA_LED_Y,
        ETH_LED_G               => QSFP_STA_LED_G,

        QSFP_I2C_SCL            => open,
        QSFP_I2C_SDA            => open,
        QSFP_I2C_SDA_I          =>(others => '0'),
        QSFP_I2C_SCL_I          =>(others => '0'),
        QSFP_I2C_SCL_O          => open,
        QSFP_I2C_SCL_OE         => open,
        QSFP_I2C_SDA_O          => open,
        QSFP_I2C_SDA_OE         => open,
        QSFP_I2C_DIR            => open,

        QSFP_MODSEL_N           => open,
        QSFP_LPMODE             => open,
        QSFP_RESET_N            => open,
        QSFP_MODPRS_N           => (others => '0'),
        QSFP_INT_N              => (others => '0'),

        HBM_CLK                 => (others => hbm_clk),
        HBM_RESET               => (others => hbm_reset),
        HBM_INIT_DONE           => (others => hbm_init_done),

        HBM_AXI_ARADDR          => hbm_axi_araddr,
        HBM_AXI_ARBURST         => hbm_axi_arburst,
        HBM_AXI_ARID            => hbm_axi_arid,
        HBM_AXI_ARLEN           => hbm_axi_arlen,
        HBM_AXI_ARSIZE          => hbm_axi_arsize,
        HBM_AXI_ARVALID         => hbm_axi_arvalid,
        HBM_AXI_ARREADY         => hbm_axi_arready,

        HBM_AXI_RDATA           => hbm_axi_rdata,
        HBM_AXI_RDATA_PARITY    => hbm_axi_rdata_parity,
        HBM_AXI_RID             => hbm_axi_rid,
        HBM_AXI_RLAST           => hbm_axi_rlast,
        HBM_AXI_RRESP           => hbm_axi_rresp,
        HBM_AXI_RVALID          => hbm_axi_rvalid,
        HBM_AXI_RREADY          => hbm_axi_rready,

        HBM_AXI_AWADDR          => hbm_axi_awaddr,
        HBM_AXI_AWBURST         => hbm_axi_awburst,
        HBM_AXI_AWID            => hbm_axi_awid,
        HBM_AXI_AWLEN           => hbm_axi_awlen,
        HBM_AXI_AWSIZE          => hbm_axi_awsize,
        HBM_AXI_AWVALID         => hbm_axi_awvalid,
        HBM_AXI_AWREADY         => hbm_axi_awready,

        HBM_AXI_WDATA           => hbm_axi_wdata,
        HBM_AXI_WDATA_PARITY    => hbm_axi_wdata_parity,
        HBM_AXI_WLAST           => hbm_axi_wlast,
        HBM_AXI_WSTRB           => hbm_axi_wstrb,
        HBM_AXI_WVALID          => hbm_axi_wvalid,
        HBM_AXI_WREADY          => hbm_axi_wready,

        HBM_AXI_BID             => hbm_axi_bid,
        HBM_AXI_BRESP           => hbm_axi_bresp,
        HBM_AXI_BVALID          => hbm_axi_bvalid,
        HBM_AXI_BREADY          => hbm_axi_bready,

        MEM_CLK                 => (others => '0'),
        MEM_RST                 => (others => '0'),

        -- Avalon interface to mem_tester
        MEM_AVMM_READY          => (others => '0'),
        MEM_AVMM_READ           => open,
        MEM_AVMM_WRITE          => open,
        MEM_AVMM_ADDRESS        => open,
        MEM_AVMM_BURSTCOUNT     => open,
        MEM_AVMM_WRITEDATA      => open,
        MEM_AVMM_READDATA       => (others => (others => '0')),
        MEM_AVMM_READDATAVALID  => (others => '0'),

        MEM_REFR_PERIOD         => open,
        MEM_REFR_REQ            => open,
        MEM_REFR_ACK            => (others => '1'),

        EMIF_RST_REQ            => open,
        EMIF_RST_DONE           => (others => '0'),
        EMIF_CAL_SUCCESS        => (others => '0'),
        EMIF_ECC_USR_INT        => (others => '0'),
        EMIF_CAL_FAIL           => (others => '0'),
        EMIF_AUTO_PRECHARGE     => open,

        STATUS_LED_G            => open,
        STATUS_LED_R            => open,

        PCIE_CLK                => open,
        PCIE_RESET              => open,

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

    pcie_ref_clk_p <= (PCIE_SYSCLK1_P & PCIE_SYSCLK0_P) when PCIE_ENDPOINT_MODE = 1 else (others => PCIE_SYSCLK1_P);
    pcie_ref_clk_n <= (PCIE_SYSCLK1_N & PCIE_SYSCLK0_N) when PCIE_ENDPOINT_MODE = 1 else (others => PCIE_SYSCLK1_N);

    -- =========================================================================
    -- HBM MEMORY
    -- =========================================================================

    hbm_g: if (HBM_PORTS > 0) generate
        hbm_ibuf_i : IBUFDS
        port map (
            I  => SYSCLK3_P,
            IB => SYSCLK3_N,
            O  => hbm_sysclk_ibuf
        );

        hbm_bufg_i : BUFG
        port map (
            I => hbm_sysclk_ibuf,
            O => hbm_refclk
        );

        hbm_refclk_rst_i : xpm_cdc_async_rst
        generic map (
            DEST_SYNC_FF    => 4,
            INIT_SYNC_FF    => 1,
            RST_ACTIVE_HIGH => 1
        )
        port map (
            src_arst  => sysrst,
            dest_clk  => hbm_refclk,
            dest_arst => hbm_refclk_rst
        );

        hbm_mmcm_i : MMCME4_ADV
        generic map (
            BANDWIDTH            => "OPTIMIZED",
            CLKFBOUT_MULT_F      => 9.0, -- 9x 100 MHz = 900 MHz
            CLKFBOUT_PHASE       => 0.0,
            CLKFBOUT_USE_FINE_PS => "FALSE",
            CLKIN1_PERIOD        => 10.0, -- 100 MHz input clock
            CLKIN2_PERIOD        => 0.0,
            CLKOUT0_DIVIDE_F     => 2.0, -- 900 MHz / 2 = 450 MHz CLKOUT0
            CLKOUT0_DUTY_CYCLE   => 0.5,
            CLKOUT0_PHASE        => 0.0,
            CLKOUT0_USE_FINE_PS  => "FALSE",
            CLKOUT1_DIVIDE       => 1,
            CLKOUT1_DUTY_CYCLE   => 0.5,
            CLKOUT1_PHASE        => 0.0,
            CLKOUT1_USE_FINE_PS  => "FALSE",
            CLKOUT2_DIVIDE       => 1,
            CLKOUT2_DUTY_CYCLE   => 0.5,
            CLKOUT2_PHASE        => 0.0,
            CLKOUT2_USE_FINE_PS  => "FALSE",
            CLKOUT3_DIVIDE       => 1,
            CLKOUT3_DUTY_CYCLE   => 0.5,
            CLKOUT3_PHASE        => 0.0,
            CLKOUT3_USE_FINE_PS  => "FALSE",
            CLKOUT4_CASCADE      => "FALSE",
            CLKOUT4_DIVIDE       => 1,
            CLKOUT4_DUTY_CYCLE   => 0.5,
            CLKOUT4_PHASE        => 0.0,
            CLKOUT4_USE_FINE_PS  => "FALSE",
            CLKOUT5_DIVIDE       => 1,
            CLKOUT5_DUTY_CYCLE   => 0.5,
            CLKOUT5_PHASE        => 0.0,
            CLKOUT5_USE_FINE_PS  => "FALSE",
            CLKOUT6_DIVIDE       => 1,
            CLKOUT6_DUTY_CYCLE   => 0.5,
            CLKOUT6_PHASE        => 0.0,
            CLKOUT6_USE_FINE_PS  => "FALSE",
            COMPENSATION         => "AUTO",
            DIVCLK_DIVIDE        => 1,
            IS_CLKFBIN_INVERTED  => '0',
            IS_CLKIN1_INVERTED   => '0',
            IS_CLKIN2_INVERTED   => '0',
            IS_CLKINSEL_INVERTED => '0',
            IS_PSEN_INVERTED     => '0',
            IS_PSINCDEC_INVERTED => '0',
            IS_PWRDWN_INVERTED   => '0',
            IS_RST_INVERTED      => '0',
            REF_JITTER1          => 0.0,
            REF_JITTER2          => 0.0,
            SS_EN                => "FALSE",
            SS_MODE              => "CENTER_HIGH",
            SS_MOD_PERIOD        => 10000,
            STARTUP_WAIT         => "FALSE"
        )
        port map (
            CDDCDONE     => open,
            CLKFBOUT     => hbm_mmcm_clkfb,
            CLKFBOUTB    => open,
            CLKFBSTOPPED => open,
            CLKINSTOPPED => open,
            CLKOUT0      => hbm_clk_mmcm,
            CLKOUT0B     => open,
            CLKOUT1      => open,
            CLKOUT1B     => open,
            CLKOUT2      => open,
            CLKOUT2B     => open,
            CLKOUT3      => open,
            CLKOUT3B     => open,
            CLKOUT4      => open,
            CLKOUT5      => open,
            CLKOUT6      => open,

            DO           => open,
            DRDY         => open,
            LOCKED       => hbm_mmcm_lock,
            PSDONE       => open,
            CDDCREQ      => '0',
            CLKFBIN      => hbm_mmcm_clkfb,
            CLKIN1       => hbm_refclk,
            CLKIN2       => '0',
            CLKINSEL     => '1',
            DADDR        => (others => '0'),
            DCLK         => '0',
            DEN          => '0',
            DI           => (others => '0'),
            DWE          => '0',
            PSCLK        => '0',
            PSEN         => '0',
            PSINCDEC     => '0',
            PWRDWN       => '0',
            RST          => hbm_refclk_rst
        );

        hbm_clk_bufg_i : BUFG
        port map (
            I => hbm_clk_mmcm,
            O => hbm_clk
        );

        hbm_mmcm_lock_n <= not hbm_mmcm_lock;

        hbm_reset_i : xpm_cdc_async_rst
        generic map (
            DEST_SYNC_FF    => 8,
            INIT_SYNC_FF    => 1,
            RST_ACTIVE_HIGH => 1
        )
        port map (
            src_arst  => hbm_mmcm_lock_n,
            dest_arst => hbm_reset,
            dest_clk  => hbm_clk
        );

        hbm_clk_g: for i in 0 to HBM_PORTS-1 generate
            hbm_axi_aclk(i)     <= hbm_clk;
            process (hbm_axi_aclk)
            begin
                if (rising_edge(hbm_axi_aclk(i))) then
                    hbm_axi_areset_n(i) <= not hbm_reset;
                end if;
            end process;
        end generate;

        hbm_apb_clk     <= hbm_refclk;
        hbm_apb_reset_n <= not sysrst;

        hbm_ready_sync_g: for i in 0 to 2-1 generate -- Two HBM stack
            hbm_ready_sync_i : xpm_cdc_single
            generic map (
                DEST_SYNC_FF   => 4,
                INIT_SYNC_FF   => 0,
                SIM_ASSERT_CHK => 0,
                SRC_INPUT_REG  => 0
            )
            port map (
                dest_out => hbm_ready_sync(i),
                dest_clk => hbm_clk,
                src_clk  => hbm_apb_clk,
                src_in   => hbm_ready(i)
            );
        end generate;

        hbm_init_done <= hbm_ready_sync(0) and hbm_ready_sync(1);

        HBM_CATTRIP <= hbm0_cattrip or hbm1_cattrip;

        hbm_i : hbm_ip
        PORT MAP (
            HBM_REF_CLK_0 => hbm_refclk,
            HBM_REF_CLK_1 => hbm_refclk,
            AXI_00_ACLK => hbm_axi_aclk(0),
            AXI_00_ARESET_N => hbm_axi_areset_n(0),
            AXI_00_ARADDR => hbm_axi_araddr(0),
            AXI_00_ARBURST => hbm_axi_arburst(0),
            AXI_00_ARID => hbm_axi_arid(0),
            AXI_00_ARLEN => hbm_axi_arlen(0),
            AXI_00_ARSIZE => hbm_axi_arsize(0),
            AXI_00_ARVALID => hbm_axi_arvalid(0),
            AXI_00_AWADDR => hbm_axi_awaddr(0),
            AXI_00_AWBURST => hbm_axi_awburst(0),
            AXI_00_AWID => hbm_axi_awid(0),
            AXI_00_AWLEN => hbm_axi_awlen(0),
            AXI_00_AWSIZE => hbm_axi_awsize(0),
            AXI_00_AWVALID => hbm_axi_awvalid(0),
            AXI_00_RREADY => hbm_axi_rready(0),
            AXI_00_BREADY => hbm_axi_bready(0),
            AXI_00_WDATA => hbm_axi_wdata(0),
            AXI_00_WLAST => hbm_axi_wlast(0),
            AXI_00_WSTRB => hbm_axi_wstrb(0),
            AXI_00_WDATA_PARITY => hbm_axi_wdata_parity(0),
            AXI_00_WVALID => hbm_axi_wvalid(0),
            AXI_01_ACLK => hbm_axi_aclk(1),
            AXI_01_ARESET_N => hbm_axi_areset_n(1),
            AXI_01_ARADDR => hbm_axi_araddr(1),
            AXI_01_ARBURST => hbm_axi_arburst(1),
            AXI_01_ARID => hbm_axi_arid(1),
            AXI_01_ARLEN => hbm_axi_arlen(1),
            AXI_01_ARSIZE => hbm_axi_arsize(1),
            AXI_01_ARVALID => hbm_axi_arvalid(1),
            AXI_01_AWADDR => hbm_axi_awaddr(1),
            AXI_01_AWBURST => hbm_axi_awburst(1),
            AXI_01_AWID => hbm_axi_awid(1),
            AXI_01_AWLEN => hbm_axi_awlen(1),
            AXI_01_AWSIZE => hbm_axi_awsize(1),
            AXI_01_AWVALID => hbm_axi_awvalid(1),
            AXI_01_RREADY => hbm_axi_rready(1),
            AXI_01_BREADY => hbm_axi_bready(1),
            AXI_01_WDATA => hbm_axi_wdata(1),
            AXI_01_WLAST => hbm_axi_wlast(1),
            AXI_01_WSTRB => hbm_axi_wstrb(1),
            AXI_01_WDATA_PARITY => hbm_axi_wdata_parity(1),
            AXI_01_WVALID => hbm_axi_wvalid(1),
            AXI_02_ACLK => hbm_axi_aclk(2),
            AXI_02_ARESET_N => hbm_axi_areset_n(2),
            AXI_02_ARADDR => hbm_axi_araddr(2),
            AXI_02_ARBURST => hbm_axi_arburst(2),
            AXI_02_ARID => hbm_axi_arid(2),
            AXI_02_ARLEN => hbm_axi_arlen(2),
            AXI_02_ARSIZE => hbm_axi_arsize(2),
            AXI_02_ARVALID => hbm_axi_arvalid(2),
            AXI_02_AWADDR => hbm_axi_awaddr(2),
            AXI_02_AWBURST => hbm_axi_awburst(2),
            AXI_02_AWID => hbm_axi_awid(2),
            AXI_02_AWLEN => hbm_axi_awlen(2),
            AXI_02_AWSIZE => hbm_axi_awsize(2),
            AXI_02_AWVALID => hbm_axi_awvalid(2),
            AXI_02_RREADY => hbm_axi_rready(2),
            AXI_02_BREADY => hbm_axi_bready(2),
            AXI_02_WDATA => hbm_axi_wdata(2),
            AXI_02_WLAST => hbm_axi_wlast(2),
            AXI_02_WSTRB => hbm_axi_wstrb(2),
            AXI_02_WDATA_PARITY => hbm_axi_wdata_parity(2),
            AXI_02_WVALID => hbm_axi_wvalid(2),
            AXI_03_ACLK => hbm_axi_aclk(3),
            AXI_03_ARESET_N => hbm_axi_areset_n(3),
            AXI_03_ARADDR => hbm_axi_araddr(3),
            AXI_03_ARBURST => hbm_axi_arburst(3),
            AXI_03_ARID => hbm_axi_arid(3),
            AXI_03_ARLEN => hbm_axi_arlen(3),
            AXI_03_ARSIZE => hbm_axi_arsize(3),
            AXI_03_ARVALID => hbm_axi_arvalid(3),
            AXI_03_AWADDR => hbm_axi_awaddr(3),
            AXI_03_AWBURST => hbm_axi_awburst(3),
            AXI_03_AWID => hbm_axi_awid(3),
            AXI_03_AWLEN => hbm_axi_awlen(3),
            AXI_03_AWSIZE => hbm_axi_awsize(3),
            AXI_03_AWVALID => hbm_axi_awvalid(3),
            AXI_03_RREADY => hbm_axi_rready(3),
            AXI_03_BREADY => hbm_axi_bready(3),
            AXI_03_WDATA => hbm_axi_wdata(3),
            AXI_03_WLAST => hbm_axi_wlast(3),
            AXI_03_WSTRB => hbm_axi_wstrb(3),
            AXI_03_WDATA_PARITY => hbm_axi_wdata_parity(3),
            AXI_03_WVALID => hbm_axi_wvalid(3),
            AXI_04_ACLK => hbm_axi_aclk(4),
            AXI_04_ARESET_N => hbm_axi_areset_n(4),
            AXI_04_ARADDR => hbm_axi_araddr(4),
            AXI_04_ARBURST => hbm_axi_arburst(4),
            AXI_04_ARID => hbm_axi_arid(4),
            AXI_04_ARLEN => hbm_axi_arlen(4),
            AXI_04_ARSIZE => hbm_axi_arsize(4),
            AXI_04_ARVALID => hbm_axi_arvalid(4),
            AXI_04_AWADDR => hbm_axi_awaddr(4),
            AXI_04_AWBURST => hbm_axi_awburst(4),
            AXI_04_AWID => hbm_axi_awid(4),
            AXI_04_AWLEN => hbm_axi_awlen(4),
            AXI_04_AWSIZE => hbm_axi_awsize(4),
            AXI_04_AWVALID => hbm_axi_awvalid(4),
            AXI_04_RREADY => hbm_axi_rready(4),
            AXI_04_BREADY => hbm_axi_bready(4),
            AXI_04_WDATA => hbm_axi_wdata(4),
            AXI_04_WLAST => hbm_axi_wlast(4),
            AXI_04_WSTRB => hbm_axi_wstrb(4),
            AXI_04_WDATA_PARITY => hbm_axi_wdata_parity(4),
            AXI_04_WVALID => hbm_axi_wvalid(4),
            AXI_05_ACLK => hbm_axi_aclk(5),
            AXI_05_ARESET_N => hbm_axi_areset_n(5),
            AXI_05_ARADDR => hbm_axi_araddr(5),
            AXI_05_ARBURST => hbm_axi_arburst(5),
            AXI_05_ARID => hbm_axi_arid(5),
            AXI_05_ARLEN => hbm_axi_arlen(5),
            AXI_05_ARSIZE => hbm_axi_arsize(5),
            AXI_05_ARVALID => hbm_axi_arvalid(5),
            AXI_05_AWADDR => hbm_axi_awaddr(5),
            AXI_05_AWBURST => hbm_axi_awburst(5),
            AXI_05_AWID => hbm_axi_awid(5),
            AXI_05_AWLEN => hbm_axi_awlen(5),
            AXI_05_AWSIZE => hbm_axi_awsize(5),
            AXI_05_AWVALID => hbm_axi_awvalid(5),
            AXI_05_RREADY => hbm_axi_rready(5),
            AXI_05_BREADY => hbm_axi_bready(5),
            AXI_05_WDATA => hbm_axi_wdata(5),
            AXI_05_WLAST => hbm_axi_wlast(5),
            AXI_05_WSTRB => hbm_axi_wstrb(5),
            AXI_05_WDATA_PARITY => hbm_axi_wdata_parity(5),
            AXI_05_WVALID => hbm_axi_wvalid(5),
            AXI_06_ACLK => hbm_axi_aclk(6),
            AXI_06_ARESET_N => hbm_axi_areset_n(6),
            AXI_06_ARADDR => hbm_axi_araddr(6),
            AXI_06_ARBURST => hbm_axi_arburst(6),
            AXI_06_ARID => hbm_axi_arid(6),
            AXI_06_ARLEN => hbm_axi_arlen(6),
            AXI_06_ARSIZE => hbm_axi_arsize(6),
            AXI_06_ARVALID => hbm_axi_arvalid(6),
            AXI_06_AWADDR => hbm_axi_awaddr(6),
            AXI_06_AWBURST => hbm_axi_awburst(6),
            AXI_06_AWID => hbm_axi_awid(6),
            AXI_06_AWLEN => hbm_axi_awlen(6),
            AXI_06_AWSIZE => hbm_axi_awsize(6),
            AXI_06_AWVALID => hbm_axi_awvalid(6),
            AXI_06_RREADY => hbm_axi_rready(6),
            AXI_06_BREADY => hbm_axi_bready(6),
            AXI_06_WDATA => hbm_axi_wdata(6),
            AXI_06_WLAST => hbm_axi_wlast(6),
            AXI_06_WSTRB => hbm_axi_wstrb(6),
            AXI_06_WDATA_PARITY => hbm_axi_wdata_parity(6),
            AXI_06_WVALID => hbm_axi_wvalid(6),
            AXI_07_ACLK => hbm_axi_aclk(7),
            AXI_07_ARESET_N => hbm_axi_areset_n(7),
            AXI_07_ARADDR => hbm_axi_araddr(7),
            AXI_07_ARBURST => hbm_axi_arburst(7),
            AXI_07_ARID => hbm_axi_arid(7),
            AXI_07_ARLEN => hbm_axi_arlen(7),
            AXI_07_ARSIZE => hbm_axi_arsize(7),
            AXI_07_ARVALID => hbm_axi_arvalid(7),
            AXI_07_AWADDR => hbm_axi_awaddr(7),
            AXI_07_AWBURST => hbm_axi_awburst(7),
            AXI_07_AWID => hbm_axi_awid(7),
            AXI_07_AWLEN => hbm_axi_awlen(7),
            AXI_07_AWSIZE => hbm_axi_awsize(7),
            AXI_07_AWVALID => hbm_axi_awvalid(7),
            AXI_07_RREADY => hbm_axi_rready(7),
            AXI_07_BREADY => hbm_axi_bready(7),
            AXI_07_WDATA => hbm_axi_wdata(7),
            AXI_07_WLAST => hbm_axi_wlast(7),
            AXI_07_WSTRB => hbm_axi_wstrb(7),
            AXI_07_WDATA_PARITY => hbm_axi_wdata_parity(7),
            AXI_07_WVALID => hbm_axi_wvalid(7),
            AXI_08_ACLK => hbm_axi_aclk(8),
            AXI_08_ARESET_N => hbm_axi_areset_n(8),
            AXI_08_ARADDR => hbm_axi_araddr(8),
            AXI_08_ARBURST => hbm_axi_arburst(8),
            AXI_08_ARID => hbm_axi_arid(8),
            AXI_08_ARLEN => hbm_axi_arlen(8),
            AXI_08_ARSIZE => hbm_axi_arsize(8),
            AXI_08_ARVALID => hbm_axi_arvalid(8),
            AXI_08_AWADDR => hbm_axi_awaddr(8),
            AXI_08_AWBURST => hbm_axi_awburst(8),
            AXI_08_AWID => hbm_axi_awid(8),
            AXI_08_AWLEN => hbm_axi_awlen(8),
            AXI_08_AWSIZE => hbm_axi_awsize(8),
            AXI_08_AWVALID => hbm_axi_awvalid(8),
            AXI_08_RREADY => hbm_axi_rready(8),
            AXI_08_BREADY => hbm_axi_bready(8),
            AXI_08_WDATA => hbm_axi_wdata(8),
            AXI_08_WLAST => hbm_axi_wlast(8),
            AXI_08_WSTRB => hbm_axi_wstrb(8),
            AXI_08_WDATA_PARITY => hbm_axi_wdata_parity(8),
            AXI_08_WVALID => hbm_axi_wvalid(8),
            AXI_09_ACLK => hbm_axi_aclk(9),
            AXI_09_ARESET_N => hbm_axi_areset_n(9),
            AXI_09_ARADDR => hbm_axi_araddr(9),
            AXI_09_ARBURST => hbm_axi_arburst(9),
            AXI_09_ARID => hbm_axi_arid(9),
            AXI_09_ARLEN => hbm_axi_arlen(9),
            AXI_09_ARSIZE => hbm_axi_arsize(9),
            AXI_09_ARVALID => hbm_axi_arvalid(9),
            AXI_09_AWADDR => hbm_axi_awaddr(9),
            AXI_09_AWBURST => hbm_axi_awburst(9),
            AXI_09_AWID => hbm_axi_awid(9),
            AXI_09_AWLEN => hbm_axi_awlen(9),
            AXI_09_AWSIZE => hbm_axi_awsize(9),
            AXI_09_AWVALID => hbm_axi_awvalid(9),
            AXI_09_RREADY => hbm_axi_rready(9),
            AXI_09_BREADY => hbm_axi_bready(9),
            AXI_09_WDATA => hbm_axi_wdata(9),
            AXI_09_WLAST => hbm_axi_wlast(9),
            AXI_09_WSTRB => hbm_axi_wstrb(9),
            AXI_09_WDATA_PARITY => hbm_axi_wdata_parity(9),
            AXI_09_WVALID => hbm_axi_wvalid(9),
            AXI_10_ACLK => hbm_axi_aclk(10),
            AXI_10_ARESET_N => hbm_axi_areset_n(10),
            AXI_10_ARADDR => hbm_axi_araddr(10),
            AXI_10_ARBURST => hbm_axi_arburst(10),
            AXI_10_ARID => hbm_axi_arid(10),
            AXI_10_ARLEN => hbm_axi_arlen(10),
            AXI_10_ARSIZE => hbm_axi_arsize(10),
            AXI_10_ARVALID => hbm_axi_arvalid(10),
            AXI_10_AWADDR => hbm_axi_awaddr(10),
            AXI_10_AWBURST => hbm_axi_awburst(10),
            AXI_10_AWID => hbm_axi_awid(10),
            AXI_10_AWLEN => hbm_axi_awlen(10),
            AXI_10_AWSIZE => hbm_axi_awsize(10),
            AXI_10_AWVALID => hbm_axi_awvalid(10),
            AXI_10_RREADY => hbm_axi_rready(10),
            AXI_10_BREADY => hbm_axi_bready(10),
            AXI_10_WDATA => hbm_axi_wdata(10),
            AXI_10_WLAST => hbm_axi_wlast(10),
            AXI_10_WSTRB => hbm_axi_wstrb(10),
            AXI_10_WDATA_PARITY => hbm_axi_wdata_parity(10),
            AXI_10_WVALID => hbm_axi_wvalid(10),
            AXI_11_ACLK => hbm_axi_aclk(11),
            AXI_11_ARESET_N => hbm_axi_areset_n(11),
            AXI_11_ARADDR => hbm_axi_araddr(11),
            AXI_11_ARBURST => hbm_axi_arburst(11),
            AXI_11_ARID => hbm_axi_arid(11),
            AXI_11_ARLEN => hbm_axi_arlen(11),
            AXI_11_ARSIZE => hbm_axi_arsize(11),
            AXI_11_ARVALID => hbm_axi_arvalid(11),
            AXI_11_AWADDR => hbm_axi_awaddr(11),
            AXI_11_AWBURST => hbm_axi_awburst(11),
            AXI_11_AWID => hbm_axi_awid(11),
            AXI_11_AWLEN => hbm_axi_awlen(11),
            AXI_11_AWSIZE => hbm_axi_awsize(11),
            AXI_11_AWVALID => hbm_axi_awvalid(11),
            AXI_11_RREADY => hbm_axi_rready(11),
            AXI_11_BREADY => hbm_axi_bready(11),
            AXI_11_WDATA => hbm_axi_wdata(11),
            AXI_11_WLAST => hbm_axi_wlast(11),
            AXI_11_WSTRB => hbm_axi_wstrb(11),
            AXI_11_WDATA_PARITY => hbm_axi_wdata_parity(11),
            AXI_11_WVALID => hbm_axi_wvalid(11),
            AXI_12_ACLK => hbm_axi_aclk(12),
            AXI_12_ARESET_N => hbm_axi_areset_n(12),
            AXI_12_ARADDR => hbm_axi_araddr(12),
            AXI_12_ARBURST => hbm_axi_arburst(12),
            AXI_12_ARID => hbm_axi_arid(12),
            AXI_12_ARLEN => hbm_axi_arlen(12),
            AXI_12_ARSIZE => hbm_axi_arsize(12),
            AXI_12_ARVALID => hbm_axi_arvalid(12),
            AXI_12_AWADDR => hbm_axi_awaddr(12),
            AXI_12_AWBURST => hbm_axi_awburst(12),
            AXI_12_AWID => hbm_axi_awid(12),
            AXI_12_AWLEN => hbm_axi_awlen(12),
            AXI_12_AWSIZE => hbm_axi_awsize(12),
            AXI_12_AWVALID => hbm_axi_awvalid(12),
            AXI_12_RREADY => hbm_axi_rready(12),
            AXI_12_BREADY => hbm_axi_bready(12),
            AXI_12_WDATA => hbm_axi_wdata(12),
            AXI_12_WLAST => hbm_axi_wlast(12),
            AXI_12_WSTRB => hbm_axi_wstrb(12),
            AXI_12_WDATA_PARITY => hbm_axi_wdata_parity(12),
            AXI_12_WVALID => hbm_axi_wvalid(12),
            AXI_13_ACLK => hbm_axi_aclk(13),
            AXI_13_ARESET_N => hbm_axi_areset_n(13),
            AXI_13_ARADDR => hbm_axi_araddr(13),
            AXI_13_ARBURST => hbm_axi_arburst(13),
            AXI_13_ARID => hbm_axi_arid(13),
            AXI_13_ARLEN => hbm_axi_arlen(13),
            AXI_13_ARSIZE => hbm_axi_arsize(13),
            AXI_13_ARVALID => hbm_axi_arvalid(13),
            AXI_13_AWADDR => hbm_axi_awaddr(13),
            AXI_13_AWBURST => hbm_axi_awburst(13),
            AXI_13_AWID => hbm_axi_awid(13),
            AXI_13_AWLEN => hbm_axi_awlen(13),
            AXI_13_AWSIZE => hbm_axi_awsize(13),
            AXI_13_AWVALID => hbm_axi_awvalid(13),
            AXI_13_RREADY => hbm_axi_rready(13),
            AXI_13_BREADY => hbm_axi_bready(13),
            AXI_13_WDATA => hbm_axi_wdata(13),
            AXI_13_WLAST => hbm_axi_wlast(13),
            AXI_13_WSTRB => hbm_axi_wstrb(13),
            AXI_13_WDATA_PARITY => hbm_axi_wdata_parity(13),
            AXI_13_WVALID => hbm_axi_wvalid(13),
            AXI_14_ACLK => hbm_axi_aclk(14),
            AXI_14_ARESET_N => hbm_axi_areset_n(14),
            AXI_14_ARADDR => hbm_axi_araddr(14),
            AXI_14_ARBURST => hbm_axi_arburst(14),
            AXI_14_ARID => hbm_axi_arid(14),
            AXI_14_ARLEN => hbm_axi_arlen(14),
            AXI_14_ARSIZE => hbm_axi_arsize(14),
            AXI_14_ARVALID => hbm_axi_arvalid(14),
            AXI_14_AWADDR => hbm_axi_awaddr(14),
            AXI_14_AWBURST => hbm_axi_awburst(14),
            AXI_14_AWID => hbm_axi_awid(14),
            AXI_14_AWLEN => hbm_axi_awlen(14),
            AXI_14_AWSIZE => hbm_axi_awsize(14),
            AXI_14_AWVALID => hbm_axi_awvalid(14),
            AXI_14_RREADY => hbm_axi_rready(14),
            AXI_14_BREADY => hbm_axi_bready(14),
            AXI_14_WDATA => hbm_axi_wdata(14),
            AXI_14_WLAST => hbm_axi_wlast(14),
            AXI_14_WSTRB => hbm_axi_wstrb(14),
            AXI_14_WDATA_PARITY => hbm_axi_wdata_parity(14),
            AXI_14_WVALID => hbm_axi_wvalid(14),
            AXI_15_ACLK => hbm_axi_aclk(15),
            AXI_15_ARESET_N => hbm_axi_areset_n(15),
            AXI_15_ARADDR => hbm_axi_araddr(15),
            AXI_15_ARBURST => hbm_axi_arburst(15),
            AXI_15_ARID => hbm_axi_arid(15),
            AXI_15_ARLEN => hbm_axi_arlen(15),
            AXI_15_ARSIZE => hbm_axi_arsize(15),
            AXI_15_ARVALID => hbm_axi_arvalid(15),
            AXI_15_AWADDR => hbm_axi_awaddr(15),
            AXI_15_AWBURST => hbm_axi_awburst(15),
            AXI_15_AWID => hbm_axi_awid(15),
            AXI_15_AWLEN => hbm_axi_awlen(15),
            AXI_15_AWSIZE => hbm_axi_awsize(15),
            AXI_15_AWVALID => hbm_axi_awvalid(15),
            AXI_15_RREADY => hbm_axi_rready(15),
            AXI_15_BREADY => hbm_axi_bready(15),
            AXI_15_WDATA => hbm_axi_wdata(15),
            AXI_15_WLAST => hbm_axi_wlast(15),
            AXI_15_WSTRB => hbm_axi_wstrb(15),
            AXI_15_WDATA_PARITY => hbm_axi_wdata_parity(15),
            AXI_15_WVALID => hbm_axi_wvalid(15),
            AXI_16_ACLK => hbm_axi_aclk(16),
            AXI_16_ARESET_N => hbm_axi_areset_n(16),
            AXI_16_ARADDR => hbm_axi_araddr(16),
            AXI_16_ARBURST => hbm_axi_arburst(16),
            AXI_16_ARID => hbm_axi_arid(16),
            AXI_16_ARLEN => hbm_axi_arlen(16),
            AXI_16_ARSIZE => hbm_axi_arsize(16),
            AXI_16_ARVALID => hbm_axi_arvalid(16),
            AXI_16_AWADDR => hbm_axi_awaddr(16),
            AXI_16_AWBURST => hbm_axi_awburst(16),
            AXI_16_AWID => hbm_axi_awid(16),
            AXI_16_AWLEN => hbm_axi_awlen(16),
            AXI_16_AWSIZE => hbm_axi_awsize(16),
            AXI_16_AWVALID => hbm_axi_awvalid(16),
            AXI_16_RREADY => hbm_axi_rready(16),
            AXI_16_BREADY => hbm_axi_bready(16),
            AXI_16_WDATA => hbm_axi_wdata(16),
            AXI_16_WLAST => hbm_axi_wlast(16),
            AXI_16_WSTRB => hbm_axi_wstrb(16),
            AXI_16_WDATA_PARITY => hbm_axi_wdata_parity(16),
            AXI_16_WVALID => hbm_axi_wvalid(16),
            AXI_17_ACLK => hbm_axi_aclk(17),
            AXI_17_ARESET_N => hbm_axi_areset_n(17),
            AXI_17_ARADDR => hbm_axi_araddr(17),
            AXI_17_ARBURST => hbm_axi_arburst(17),
            AXI_17_ARID => hbm_axi_arid(17),
            AXI_17_ARLEN => hbm_axi_arlen(17),
            AXI_17_ARSIZE => hbm_axi_arsize(17),
            AXI_17_ARVALID => hbm_axi_arvalid(17),
            AXI_17_AWADDR => hbm_axi_awaddr(17),
            AXI_17_AWBURST => hbm_axi_awburst(17),
            AXI_17_AWID => hbm_axi_awid(17),
            AXI_17_AWLEN => hbm_axi_awlen(17),
            AXI_17_AWSIZE => hbm_axi_awsize(17),
            AXI_17_AWVALID => hbm_axi_awvalid(17),
            AXI_17_RREADY => hbm_axi_rready(17),
            AXI_17_BREADY => hbm_axi_bready(17),
            AXI_17_WDATA => hbm_axi_wdata(17),
            AXI_17_WLAST => hbm_axi_wlast(17),
            AXI_17_WSTRB => hbm_axi_wstrb(17),
            AXI_17_WDATA_PARITY => hbm_axi_wdata_parity(17),
            AXI_17_WVALID => hbm_axi_wvalid(17),
            AXI_18_ACLK => hbm_axi_aclk(18),
            AXI_18_ARESET_N => hbm_axi_areset_n(18),
            AXI_18_ARADDR => hbm_axi_araddr(18),
            AXI_18_ARBURST => hbm_axi_arburst(18),
            AXI_18_ARID => hbm_axi_arid(18),
            AXI_18_ARLEN => hbm_axi_arlen(18),
            AXI_18_ARSIZE => hbm_axi_arsize(18),
            AXI_18_ARVALID => hbm_axi_arvalid(18),
            AXI_18_AWADDR => hbm_axi_awaddr(18),
            AXI_18_AWBURST => hbm_axi_awburst(18),
            AXI_18_AWID => hbm_axi_awid(18),
            AXI_18_AWLEN => hbm_axi_awlen(18),
            AXI_18_AWSIZE => hbm_axi_awsize(18),
            AXI_18_AWVALID => hbm_axi_awvalid(18),
            AXI_18_RREADY => hbm_axi_rready(18),
            AXI_18_BREADY => hbm_axi_bready(18),
            AXI_18_WDATA => hbm_axi_wdata(18),
            AXI_18_WLAST => hbm_axi_wlast(18),
            AXI_18_WSTRB => hbm_axi_wstrb(18),
            AXI_18_WDATA_PARITY => hbm_axi_wdata_parity(18),
            AXI_18_WVALID => hbm_axi_wvalid(18),
            AXI_19_ACLK => hbm_axi_aclk(19),
            AXI_19_ARESET_N => hbm_axi_areset_n(19),
            AXI_19_ARADDR => hbm_axi_araddr(19),
            AXI_19_ARBURST => hbm_axi_arburst(19),
            AXI_19_ARID => hbm_axi_arid(19),
            AXI_19_ARLEN => hbm_axi_arlen(19),
            AXI_19_ARSIZE => hbm_axi_arsize(19),
            AXI_19_ARVALID => hbm_axi_arvalid(19),
            AXI_19_AWADDR => hbm_axi_awaddr(19),
            AXI_19_AWBURST => hbm_axi_awburst(19),
            AXI_19_AWID => hbm_axi_awid(19),
            AXI_19_AWLEN => hbm_axi_awlen(19),
            AXI_19_AWSIZE => hbm_axi_awsize(19),
            AXI_19_AWVALID => hbm_axi_awvalid(19),
            AXI_19_RREADY => hbm_axi_rready(19),
            AXI_19_BREADY => hbm_axi_bready(19),
            AXI_19_WDATA => hbm_axi_wdata(19),
            AXI_19_WLAST => hbm_axi_wlast(19),
            AXI_19_WSTRB => hbm_axi_wstrb(19),
            AXI_19_WDATA_PARITY => hbm_axi_wdata_parity(19),
            AXI_19_WVALID => hbm_axi_wvalid(19),
            AXI_20_ACLK => hbm_axi_aclk(20),
            AXI_20_ARESET_N => hbm_axi_areset_n(20),
            AXI_20_ARADDR => hbm_axi_araddr(20),
            AXI_20_ARBURST => hbm_axi_arburst(20),
            AXI_20_ARID => hbm_axi_arid(20),
            AXI_20_ARLEN => hbm_axi_arlen(20),
            AXI_20_ARSIZE => hbm_axi_arsize(20),
            AXI_20_ARVALID => hbm_axi_arvalid(20),
            AXI_20_AWADDR => hbm_axi_awaddr(20),
            AXI_20_AWBURST => hbm_axi_awburst(20),
            AXI_20_AWID => hbm_axi_awid(20),
            AXI_20_AWLEN => hbm_axi_awlen(20),
            AXI_20_AWSIZE => hbm_axi_awsize(20),
            AXI_20_AWVALID => hbm_axi_awvalid(20),
            AXI_20_RREADY => hbm_axi_rready(20),
            AXI_20_BREADY => hbm_axi_bready(20),
            AXI_20_WDATA => hbm_axi_wdata(20),
            AXI_20_WLAST => hbm_axi_wlast(20),
            AXI_20_WSTRB => hbm_axi_wstrb(20),
            AXI_20_WDATA_PARITY => hbm_axi_wdata_parity(20),
            AXI_20_WVALID => hbm_axi_wvalid(20),
            AXI_21_ACLK => hbm_axi_aclk(21),
            AXI_21_ARESET_N => hbm_axi_areset_n(21),
            AXI_21_ARADDR => hbm_axi_araddr(21),
            AXI_21_ARBURST => hbm_axi_arburst(21),
            AXI_21_ARID => hbm_axi_arid(21),
            AXI_21_ARLEN => hbm_axi_arlen(21),
            AXI_21_ARSIZE => hbm_axi_arsize(21),
            AXI_21_ARVALID => hbm_axi_arvalid(21),
            AXI_21_AWADDR => hbm_axi_awaddr(21),
            AXI_21_AWBURST => hbm_axi_awburst(21),
            AXI_21_AWID => hbm_axi_awid(21),
            AXI_21_AWLEN => hbm_axi_awlen(21),
            AXI_21_AWSIZE => hbm_axi_awsize(21),
            AXI_21_AWVALID => hbm_axi_awvalid(21),
            AXI_21_RREADY => hbm_axi_rready(21),
            AXI_21_BREADY => hbm_axi_bready(21),
            AXI_21_WDATA => hbm_axi_wdata(21),
            AXI_21_WLAST => hbm_axi_wlast(21),
            AXI_21_WSTRB => hbm_axi_wstrb(21),
            AXI_21_WDATA_PARITY => hbm_axi_wdata_parity(21),
            AXI_21_WVALID => hbm_axi_wvalid(21),
            AXI_22_ACLK => hbm_axi_aclk(22),
            AXI_22_ARESET_N => hbm_axi_areset_n(22),
            AXI_22_ARADDR => hbm_axi_araddr(22),
            AXI_22_ARBURST => hbm_axi_arburst(22),
            AXI_22_ARID => hbm_axi_arid(22),
            AXI_22_ARLEN => hbm_axi_arlen(22),
            AXI_22_ARSIZE => hbm_axi_arsize(22),
            AXI_22_ARVALID => hbm_axi_arvalid(22),
            AXI_22_AWADDR => hbm_axi_awaddr(22),
            AXI_22_AWBURST => hbm_axi_awburst(22),
            AXI_22_AWID => hbm_axi_awid(22),
            AXI_22_AWLEN => hbm_axi_awlen(22),
            AXI_22_AWSIZE => hbm_axi_awsize(22),
            AXI_22_AWVALID => hbm_axi_awvalid(22),
            AXI_22_RREADY => hbm_axi_rready(22),
            AXI_22_BREADY => hbm_axi_bready(22),
            AXI_22_WDATA => hbm_axi_wdata(22),
            AXI_22_WLAST => hbm_axi_wlast(22),
            AXI_22_WSTRB => hbm_axi_wstrb(22),
            AXI_22_WDATA_PARITY => hbm_axi_wdata_parity(22),
            AXI_22_WVALID => hbm_axi_wvalid(22),
            AXI_23_ACLK => hbm_axi_aclk(23),
            AXI_23_ARESET_N => hbm_axi_areset_n(23),
            AXI_23_ARADDR => hbm_axi_araddr(23),
            AXI_23_ARBURST => hbm_axi_arburst(23),
            AXI_23_ARID => hbm_axi_arid(23),
            AXI_23_ARLEN => hbm_axi_arlen(23),
            AXI_23_ARSIZE => hbm_axi_arsize(23),
            AXI_23_ARVALID => hbm_axi_arvalid(23),
            AXI_23_AWADDR => hbm_axi_awaddr(23),
            AXI_23_AWBURST => hbm_axi_awburst(23),
            AXI_23_AWID => hbm_axi_awid(23),
            AXI_23_AWLEN => hbm_axi_awlen(23),
            AXI_23_AWSIZE => hbm_axi_awsize(23),
            AXI_23_AWVALID => hbm_axi_awvalid(23),
            AXI_23_RREADY => hbm_axi_rready(23),
            AXI_23_BREADY => hbm_axi_bready(23),
            AXI_23_WDATA => hbm_axi_wdata(23),
            AXI_23_WLAST => hbm_axi_wlast(23),
            AXI_23_WSTRB => hbm_axi_wstrb(23),
            AXI_23_WDATA_PARITY => hbm_axi_wdata_parity(23),
            AXI_23_WVALID => hbm_axi_wvalid(23),
            AXI_24_ACLK => hbm_axi_aclk(24),
            AXI_24_ARESET_N => hbm_axi_areset_n(24),
            AXI_24_ARADDR => hbm_axi_araddr(24),
            AXI_24_ARBURST => hbm_axi_arburst(24),
            AXI_24_ARID => hbm_axi_arid(24),
            AXI_24_ARLEN => hbm_axi_arlen(24),
            AXI_24_ARSIZE => hbm_axi_arsize(24),
            AXI_24_ARVALID => hbm_axi_arvalid(24),
            AXI_24_AWADDR => hbm_axi_awaddr(24),
            AXI_24_AWBURST => hbm_axi_awburst(24),
            AXI_24_AWID => hbm_axi_awid(24),
            AXI_24_AWLEN => hbm_axi_awlen(24),
            AXI_24_AWSIZE => hbm_axi_awsize(24),
            AXI_24_AWVALID => hbm_axi_awvalid(24),
            AXI_24_RREADY => hbm_axi_rready(24),
            AXI_24_BREADY => hbm_axi_bready(24),
            AXI_24_WDATA => hbm_axi_wdata(24),
            AXI_24_WLAST => hbm_axi_wlast(24),
            AXI_24_WSTRB => hbm_axi_wstrb(24),
            AXI_24_WDATA_PARITY => hbm_axi_wdata_parity(24),
            AXI_24_WVALID => hbm_axi_wvalid(24),
            AXI_25_ACLK => hbm_axi_aclk(25),
            AXI_25_ARESET_N => hbm_axi_areset_n(25),
            AXI_25_ARADDR => hbm_axi_araddr(25),
            AXI_25_ARBURST => hbm_axi_arburst(25),
            AXI_25_ARID => hbm_axi_arid(25),
            AXI_25_ARLEN => hbm_axi_arlen(25),
            AXI_25_ARSIZE => hbm_axi_arsize(25),
            AXI_25_ARVALID => hbm_axi_arvalid(25),
            AXI_25_AWADDR => hbm_axi_awaddr(25),
            AXI_25_AWBURST => hbm_axi_awburst(25),
            AXI_25_AWID => hbm_axi_awid(25),
            AXI_25_AWLEN => hbm_axi_awlen(25),
            AXI_25_AWSIZE => hbm_axi_awsize(25),
            AXI_25_AWVALID => hbm_axi_awvalid(25),
            AXI_25_RREADY => hbm_axi_rready(25),
            AXI_25_BREADY => hbm_axi_bready(25),
            AXI_25_WDATA => hbm_axi_wdata(25),
            AXI_25_WLAST => hbm_axi_wlast(25),
            AXI_25_WSTRB => hbm_axi_wstrb(25),
            AXI_25_WDATA_PARITY => hbm_axi_wdata_parity(25),
            AXI_25_WVALID => hbm_axi_wvalid(25),
            AXI_26_ACLK => hbm_axi_aclk(26),
            AXI_26_ARESET_N => hbm_axi_areset_n(26),
            AXI_26_ARADDR => hbm_axi_araddr(26),
            AXI_26_ARBURST => hbm_axi_arburst(26),
            AXI_26_ARID => hbm_axi_arid(26),
            AXI_26_ARLEN => hbm_axi_arlen(26),
            AXI_26_ARSIZE => hbm_axi_arsize(26),
            AXI_26_ARVALID => hbm_axi_arvalid(26),
            AXI_26_AWADDR => hbm_axi_awaddr(26),
            AXI_26_AWBURST => hbm_axi_awburst(26),
            AXI_26_AWID => hbm_axi_awid(26),
            AXI_26_AWLEN => hbm_axi_awlen(26),
            AXI_26_AWSIZE => hbm_axi_awsize(26),
            AXI_26_AWVALID => hbm_axi_awvalid(26),
            AXI_26_RREADY => hbm_axi_rready(26),
            AXI_26_BREADY => hbm_axi_bready(26),
            AXI_26_WDATA => hbm_axi_wdata(26),
            AXI_26_WLAST => hbm_axi_wlast(26),
            AXI_26_WSTRB => hbm_axi_wstrb(26),
            AXI_26_WDATA_PARITY => hbm_axi_wdata_parity(26),
            AXI_26_WVALID => hbm_axi_wvalid(26),
            AXI_27_ACLK => hbm_axi_aclk(27),
            AXI_27_ARESET_N => hbm_axi_areset_n(27),
            AXI_27_ARADDR => hbm_axi_araddr(27),
            AXI_27_ARBURST => hbm_axi_arburst(27),
            AXI_27_ARID => hbm_axi_arid(27),
            AXI_27_ARLEN => hbm_axi_arlen(27),
            AXI_27_ARSIZE => hbm_axi_arsize(27),
            AXI_27_ARVALID => hbm_axi_arvalid(27),
            AXI_27_AWADDR => hbm_axi_awaddr(27),
            AXI_27_AWBURST => hbm_axi_awburst(27),
            AXI_27_AWID => hbm_axi_awid(27),
            AXI_27_AWLEN => hbm_axi_awlen(27),
            AXI_27_AWSIZE => hbm_axi_awsize(27),
            AXI_27_AWVALID => hbm_axi_awvalid(27),
            AXI_27_RREADY => hbm_axi_rready(27),
            AXI_27_BREADY => hbm_axi_bready(27),
            AXI_27_WDATA => hbm_axi_wdata(27),
            AXI_27_WLAST => hbm_axi_wlast(27),
            AXI_27_WSTRB => hbm_axi_wstrb(27),
            AXI_27_WDATA_PARITY => hbm_axi_wdata_parity(27),
            AXI_27_WVALID => hbm_axi_wvalid(27),
            AXI_28_ACLK => hbm_axi_aclk(28),
            AXI_28_ARESET_N => hbm_axi_areset_n(28),
            AXI_28_ARADDR => hbm_axi_araddr(28),
            AXI_28_ARBURST => hbm_axi_arburst(28),
            AXI_28_ARID => hbm_axi_arid(28),
            AXI_28_ARLEN => hbm_axi_arlen(28),
            AXI_28_ARSIZE => hbm_axi_arsize(28),
            AXI_28_ARVALID => hbm_axi_arvalid(28),
            AXI_28_AWADDR => hbm_axi_awaddr(28),
            AXI_28_AWBURST => hbm_axi_awburst(28),
            AXI_28_AWID => hbm_axi_awid(28),
            AXI_28_AWLEN => hbm_axi_awlen(28),
            AXI_28_AWSIZE => hbm_axi_awsize(28),
            AXI_28_AWVALID => hbm_axi_awvalid(28),
            AXI_28_RREADY => hbm_axi_rready(28),
            AXI_28_BREADY => hbm_axi_bready(28),
            AXI_28_WDATA => hbm_axi_wdata(28),
            AXI_28_WLAST => hbm_axi_wlast(28),
            AXI_28_WSTRB => hbm_axi_wstrb(28),
            AXI_28_WDATA_PARITY => hbm_axi_wdata_parity(28),
            AXI_28_WVALID => hbm_axi_wvalid(28),
            AXI_29_ACLK => hbm_axi_aclk(29),
            AXI_29_ARESET_N => hbm_axi_areset_n(29),
            AXI_29_ARADDR => hbm_axi_araddr(29),
            AXI_29_ARBURST => hbm_axi_arburst(29),
            AXI_29_ARID => hbm_axi_arid(29),
            AXI_29_ARLEN => hbm_axi_arlen(29),
            AXI_29_ARSIZE => hbm_axi_arsize(29),
            AXI_29_ARVALID => hbm_axi_arvalid(29),
            AXI_29_AWADDR => hbm_axi_awaddr(29),
            AXI_29_AWBURST => hbm_axi_awburst(29),
            AXI_29_AWID => hbm_axi_awid(29),
            AXI_29_AWLEN => hbm_axi_awlen(29),
            AXI_29_AWSIZE => hbm_axi_awsize(29),
            AXI_29_AWVALID => hbm_axi_awvalid(29),
            AXI_29_RREADY => hbm_axi_rready(29),
            AXI_29_BREADY => hbm_axi_bready(29),
            AXI_29_WDATA => hbm_axi_wdata(29),
            AXI_29_WLAST => hbm_axi_wlast(29),
            AXI_29_WSTRB => hbm_axi_wstrb(29),
            AXI_29_WDATA_PARITY => hbm_axi_wdata_parity(29),
            AXI_29_WVALID => hbm_axi_wvalid(29),
            AXI_30_ACLK => hbm_axi_aclk(30),
            AXI_30_ARESET_N => hbm_axi_areset_n(30),
            AXI_30_ARADDR => hbm_axi_araddr(30),
            AXI_30_ARBURST => hbm_axi_arburst(30),
            AXI_30_ARID => hbm_axi_arid(30),
            AXI_30_ARLEN => hbm_axi_arlen(30),
            AXI_30_ARSIZE => hbm_axi_arsize(30),
            AXI_30_ARVALID => hbm_axi_arvalid(30),
            AXI_30_AWADDR => hbm_axi_awaddr(30),
            AXI_30_AWBURST => hbm_axi_awburst(30),
            AXI_30_AWID => hbm_axi_awid(30),
            AXI_30_AWLEN => hbm_axi_awlen(30),
            AXI_30_AWSIZE => hbm_axi_awsize(30),
            AXI_30_AWVALID => hbm_axi_awvalid(30),
            AXI_30_RREADY => hbm_axi_rready(30),
            AXI_30_BREADY => hbm_axi_bready(30),
            AXI_30_WDATA => hbm_axi_wdata(30),
            AXI_30_WLAST => hbm_axi_wlast(30),
            AXI_30_WSTRB => hbm_axi_wstrb(30),
            AXI_30_WDATA_PARITY => hbm_axi_wdata_parity(30),
            AXI_30_WVALID => hbm_axi_wvalid(30),
            AXI_31_ACLK => hbm_axi_aclk(31),
            AXI_31_ARESET_N => hbm_axi_areset_n(31),
            AXI_31_ARADDR => hbm_axi_araddr(31),
            AXI_31_ARBURST => hbm_axi_arburst(31),
            AXI_31_ARID => hbm_axi_arid(31),
            AXI_31_ARLEN => hbm_axi_arlen(31),
            AXI_31_ARSIZE => hbm_axi_arsize(31),
            AXI_31_ARVALID => hbm_axi_arvalid(31),
            AXI_31_AWADDR => hbm_axi_awaddr(31),
            AXI_31_AWBURST => hbm_axi_awburst(31),
            AXI_31_AWID => hbm_axi_awid(31),
            AXI_31_AWLEN => hbm_axi_awlen(31),
            AXI_31_AWSIZE => hbm_axi_awsize(31),
            AXI_31_AWVALID => hbm_axi_awvalid(31),
            AXI_31_RREADY => hbm_axi_rready(31),
            AXI_31_BREADY => hbm_axi_bready(31),
            AXI_31_WDATA => hbm_axi_wdata(31),
            AXI_31_WLAST => hbm_axi_wlast(31),
            AXI_31_WSTRB => hbm_axi_wstrb(31),
            AXI_31_WDATA_PARITY => hbm_axi_wdata_parity(31),
            AXI_31_WVALID => hbm_axi_wvalid(31),
            APB_0_PCLK => hbm_apb_clk,
            APB_0_PRESET_N => hbm_apb_reset_n,
            APB_1_PCLK => hbm_apb_clk,
            APB_1_PRESET_N => hbm_apb_reset_n,
            AXI_00_ARREADY => hbm_axi_arready(0),
            AXI_00_AWREADY => hbm_axi_awready(0),
            AXI_00_RDATA_PARITY => hbm_axi_rdata_parity(0),
            AXI_00_RDATA => hbm_axi_rdata(0),
            AXI_00_RID => hbm_axi_rid(0),
            AXI_00_RLAST => hbm_axi_rlast(0),
            AXI_00_RRESP => hbm_axi_rresp(0),
            AXI_00_RVALID => hbm_axi_rvalid(0),
            AXI_00_WREADY => hbm_axi_wready(0),
            AXI_00_BID => hbm_axi_bid(0),
            AXI_00_BRESP => hbm_axi_bresp(0),
            AXI_00_BVALID => hbm_axi_bvalid(0),
            AXI_01_ARREADY => hbm_axi_arready(1),
            AXI_01_AWREADY => hbm_axi_awready(1),
            AXI_01_RDATA_PARITY => hbm_axi_rdata_parity(1),
            AXI_01_RDATA => hbm_axi_rdata(1),
            AXI_01_RID => hbm_axi_rid(1),
            AXI_01_RLAST => hbm_axi_rlast(1),
            AXI_01_RRESP => hbm_axi_rresp(1),
            AXI_01_RVALID => hbm_axi_rvalid(1),
            AXI_01_WREADY => hbm_axi_wready(1),
            AXI_01_BID => hbm_axi_bid(1),
            AXI_01_BRESP => hbm_axi_bresp(1),
            AXI_01_BVALID => hbm_axi_bvalid(1),
            AXI_02_ARREADY => hbm_axi_arready(2),
            AXI_02_AWREADY => hbm_axi_awready(2),
            AXI_02_RDATA_PARITY => hbm_axi_rdata_parity(2),
            AXI_02_RDATA => hbm_axi_rdata(2),
            AXI_02_RID => hbm_axi_rid(2),
            AXI_02_RLAST => hbm_axi_rlast(2),
            AXI_02_RRESP => hbm_axi_rresp(2),
            AXI_02_RVALID => hbm_axi_rvalid(2),
            AXI_02_WREADY => hbm_axi_wready(2),
            AXI_02_BID => hbm_axi_bid(2),
            AXI_02_BRESP => hbm_axi_bresp(2),
            AXI_02_BVALID => hbm_axi_bvalid(2),
            AXI_03_ARREADY => hbm_axi_arready(3),
            AXI_03_AWREADY => hbm_axi_awready(3),
            AXI_03_RDATA_PARITY => hbm_axi_rdata_parity(3),
            AXI_03_RDATA => hbm_axi_rdata(3),
            AXI_03_RID => hbm_axi_rid(3),
            AXI_03_RLAST => hbm_axi_rlast(3),
            AXI_03_RRESP => hbm_axi_rresp(3),
            AXI_03_RVALID => hbm_axi_rvalid(3),
            AXI_03_WREADY => hbm_axi_wready(3),
            AXI_03_BID => hbm_axi_bid(3),
            AXI_03_BRESP => hbm_axi_bresp(3),
            AXI_03_BVALID => hbm_axi_bvalid(3),
            AXI_04_ARREADY => hbm_axi_arready(4),
            AXI_04_AWREADY => hbm_axi_awready(4),
            AXI_04_RDATA_PARITY => hbm_axi_rdata_parity(4),
            AXI_04_RDATA => hbm_axi_rdata(4),
            AXI_04_RID => hbm_axi_rid(4),
            AXI_04_RLAST => hbm_axi_rlast(4),
            AXI_04_RRESP => hbm_axi_rresp(4),
            AXI_04_RVALID => hbm_axi_rvalid(4),
            AXI_04_WREADY => hbm_axi_wready(4),
            AXI_04_BID => hbm_axi_bid(4),
            AXI_04_BRESP => hbm_axi_bresp(4),
            AXI_04_BVALID => hbm_axi_bvalid(4),
            AXI_05_ARREADY => hbm_axi_arready(5),
            AXI_05_AWREADY => hbm_axi_awready(5),
            AXI_05_RDATA_PARITY => hbm_axi_rdata_parity(5),
            AXI_05_RDATA => hbm_axi_rdata(5),
            AXI_05_RID => hbm_axi_rid(5),
            AXI_05_RLAST => hbm_axi_rlast(5),
            AXI_05_RRESP => hbm_axi_rresp(5),
            AXI_05_RVALID => hbm_axi_rvalid(5),
            AXI_05_WREADY => hbm_axi_wready(5),
            AXI_05_BID => hbm_axi_bid(5),
            AXI_05_BRESP => hbm_axi_bresp(5),
            AXI_05_BVALID => hbm_axi_bvalid(5),
            AXI_06_ARREADY => hbm_axi_arready(6),
            AXI_06_AWREADY => hbm_axi_awready(6),
            AXI_06_RDATA_PARITY => hbm_axi_rdata_parity(6),
            AXI_06_RDATA => hbm_axi_rdata(6),
            AXI_06_RID => hbm_axi_rid(6),
            AXI_06_RLAST => hbm_axi_rlast(6),
            AXI_06_RRESP => hbm_axi_rresp(6),
            AXI_06_RVALID => hbm_axi_rvalid(6),
            AXI_06_WREADY => hbm_axi_wready(6),
            AXI_06_BID => hbm_axi_bid(6),
            AXI_06_BRESP => hbm_axi_bresp(6),
            AXI_06_BVALID => hbm_axi_bvalid(6),
            AXI_07_ARREADY => hbm_axi_arready(7),
            AXI_07_AWREADY => hbm_axi_awready(7),
            AXI_07_RDATA_PARITY => hbm_axi_rdata_parity(7),
            AXI_07_RDATA => hbm_axi_rdata(7),
            AXI_07_RID => hbm_axi_rid(7),
            AXI_07_RLAST => hbm_axi_rlast(7),
            AXI_07_RRESP => hbm_axi_rresp(7),
            AXI_07_RVALID => hbm_axi_rvalid(7),
            AXI_07_WREADY => hbm_axi_wready(7),
            AXI_07_BID => hbm_axi_bid(7),
            AXI_07_BRESP => hbm_axi_bresp(7),
            AXI_07_BVALID => hbm_axi_bvalid(7),
            AXI_08_ARREADY => hbm_axi_arready(8),
            AXI_08_AWREADY => hbm_axi_awready(8),
            AXI_08_RDATA_PARITY => hbm_axi_rdata_parity(8),
            AXI_08_RDATA => hbm_axi_rdata(8),
            AXI_08_RID => hbm_axi_rid(8),
            AXI_08_RLAST => hbm_axi_rlast(8),
            AXI_08_RRESP => hbm_axi_rresp(8),
            AXI_08_RVALID => hbm_axi_rvalid(8),
            AXI_08_WREADY => hbm_axi_wready(8),
            AXI_08_BID => hbm_axi_bid(8),
            AXI_08_BRESP => hbm_axi_bresp(8),
            AXI_08_BVALID => hbm_axi_bvalid(8),
            AXI_09_ARREADY => hbm_axi_arready(9),
            AXI_09_AWREADY => hbm_axi_awready(9),
            AXI_09_RDATA_PARITY => hbm_axi_rdata_parity(9),
            AXI_09_RDATA => hbm_axi_rdata(9),
            AXI_09_RID => hbm_axi_rid(9),
            AXI_09_RLAST => hbm_axi_rlast(9),
            AXI_09_RRESP => hbm_axi_rresp(9),
            AXI_09_RVALID => hbm_axi_rvalid(9),
            AXI_09_WREADY => hbm_axi_wready(9),
            AXI_09_BID => hbm_axi_bid(9),
            AXI_09_BRESP => hbm_axi_bresp(9),
            AXI_09_BVALID => hbm_axi_bvalid(9),
            AXI_10_ARREADY => hbm_axi_arready(10),
            AXI_10_AWREADY => hbm_axi_awready(10),
            AXI_10_RDATA_PARITY => hbm_axi_rdata_parity(10),
            AXI_10_RDATA => hbm_axi_rdata(10),
            AXI_10_RID => hbm_axi_rid(10),
            AXI_10_RLAST => hbm_axi_rlast(10),
            AXI_10_RRESP => hbm_axi_rresp(10),
            AXI_10_RVALID => hbm_axi_rvalid(10),
            AXI_10_WREADY => hbm_axi_wready(10),
            AXI_10_BID => hbm_axi_bid(10),
            AXI_10_BRESP => hbm_axi_bresp(10),
            AXI_10_BVALID => hbm_axi_bvalid(10),
            AXI_11_ARREADY => hbm_axi_arready(11),
            AXI_11_AWREADY => hbm_axi_awready(11),
            AXI_11_RDATA_PARITY => hbm_axi_rdata_parity(11),
            AXI_11_RDATA => hbm_axi_rdata(11),
            AXI_11_RID => hbm_axi_rid(11),
            AXI_11_RLAST => hbm_axi_rlast(11),
            AXI_11_RRESP => hbm_axi_rresp(11),
            AXI_11_RVALID => hbm_axi_rvalid(11),
            AXI_11_WREADY => hbm_axi_wready(11),
            AXI_11_BID => hbm_axi_bid(11),
            AXI_11_BRESP => hbm_axi_bresp(11),
            AXI_11_BVALID => hbm_axi_bvalid(11),
            AXI_12_ARREADY => hbm_axi_arready(12),
            AXI_12_AWREADY => hbm_axi_awready(12),
            AXI_12_RDATA_PARITY => hbm_axi_rdata_parity(12),
            AXI_12_RDATA => hbm_axi_rdata(12),
            AXI_12_RID => hbm_axi_rid(12),
            AXI_12_RLAST => hbm_axi_rlast(12),
            AXI_12_RRESP => hbm_axi_rresp(12),
            AXI_12_RVALID => hbm_axi_rvalid(12),
            AXI_12_WREADY => hbm_axi_wready(12),
            AXI_12_BID => hbm_axi_bid(12),
            AXI_12_BRESP => hbm_axi_bresp(12),
            AXI_12_BVALID => hbm_axi_bvalid(12),
            AXI_13_ARREADY => hbm_axi_arready(13),
            AXI_13_AWREADY => hbm_axi_awready(13),
            AXI_13_RDATA_PARITY => hbm_axi_rdata_parity(13),
            AXI_13_RDATA => hbm_axi_rdata(13),
            AXI_13_RID => hbm_axi_rid(13),
            AXI_13_RLAST => hbm_axi_rlast(13),
            AXI_13_RRESP => hbm_axi_rresp(13),
            AXI_13_RVALID => hbm_axi_rvalid(13),
            AXI_13_WREADY => hbm_axi_wready(13),
            AXI_13_BID => hbm_axi_bid(13),
            AXI_13_BRESP => hbm_axi_bresp(13),
            AXI_13_BVALID => hbm_axi_bvalid(13),
            AXI_14_ARREADY => hbm_axi_arready(14),
            AXI_14_AWREADY => hbm_axi_awready(14),
            AXI_14_RDATA_PARITY => hbm_axi_rdata_parity(14),
            AXI_14_RDATA => hbm_axi_rdata(14),
            AXI_14_RID => hbm_axi_rid(14),
            AXI_14_RLAST => hbm_axi_rlast(14),
            AXI_14_RRESP => hbm_axi_rresp(14),
            AXI_14_RVALID => hbm_axi_rvalid(14),
            AXI_14_WREADY => hbm_axi_wready(14),
            AXI_14_BID => hbm_axi_bid(14),
            AXI_14_BRESP => hbm_axi_bresp(14),
            AXI_14_BVALID => hbm_axi_bvalid(14),
            AXI_15_ARREADY => hbm_axi_arready(15),
            AXI_15_AWREADY => hbm_axi_awready(15),
            AXI_15_RDATA_PARITY => hbm_axi_rdata_parity(15),
            AXI_15_RDATA => hbm_axi_rdata(15),
            AXI_15_RID => hbm_axi_rid(15),
            AXI_15_RLAST => hbm_axi_rlast(15),
            AXI_15_RRESP => hbm_axi_rresp(15),
            AXI_15_RVALID => hbm_axi_rvalid(15),
            AXI_15_WREADY => hbm_axi_wready(15),
            AXI_15_BID => hbm_axi_bid(15),
            AXI_15_BRESP => hbm_axi_bresp(15),
            AXI_15_BVALID => hbm_axi_bvalid(15),
            AXI_16_ARREADY => hbm_axi_arready(16),
            AXI_16_AWREADY => hbm_axi_awready(16),
            AXI_16_RDATA_PARITY => hbm_axi_rdata_parity(16),
            AXI_16_RDATA => hbm_axi_rdata(16),
            AXI_16_RID => hbm_axi_rid(16),
            AXI_16_RLAST => hbm_axi_rlast(16),
            AXI_16_RRESP => hbm_axi_rresp(16),
            AXI_16_RVALID => hbm_axi_rvalid(16),
            AXI_16_WREADY => hbm_axi_wready(16),
            AXI_16_BID => hbm_axi_bid(16),
            AXI_16_BRESP => hbm_axi_bresp(16),
            AXI_16_BVALID => hbm_axi_bvalid(16),
            AXI_17_ARREADY => hbm_axi_arready(17),
            AXI_17_AWREADY => hbm_axi_awready(17),
            AXI_17_RDATA_PARITY => hbm_axi_rdata_parity(17),
            AXI_17_RDATA => hbm_axi_rdata(17),
            AXI_17_RID => hbm_axi_rid(17),
            AXI_17_RLAST => hbm_axi_rlast(17),
            AXI_17_RRESP => hbm_axi_rresp(17),
            AXI_17_RVALID => hbm_axi_rvalid(17),
            AXI_17_WREADY => hbm_axi_wready(17),
            AXI_17_BID => hbm_axi_bid(17),
            AXI_17_BRESP => hbm_axi_bresp(17),
            AXI_17_BVALID => hbm_axi_bvalid(17),
            AXI_18_ARREADY => hbm_axi_arready(18),
            AXI_18_AWREADY => hbm_axi_awready(18),
            AXI_18_RDATA_PARITY => hbm_axi_rdata_parity(18),
            AXI_18_RDATA => hbm_axi_rdata(18),
            AXI_18_RID => hbm_axi_rid(18),
            AXI_18_RLAST => hbm_axi_rlast(18),
            AXI_18_RRESP => hbm_axi_rresp(18),
            AXI_18_RVALID => hbm_axi_rvalid(18),
            AXI_18_WREADY => hbm_axi_wready(18),
            AXI_18_BID => hbm_axi_bid(18),
            AXI_18_BRESP => hbm_axi_bresp(18),
            AXI_18_BVALID => hbm_axi_bvalid(18),
            AXI_19_ARREADY => hbm_axi_arready(19),
            AXI_19_AWREADY => hbm_axi_awready(19),
            AXI_19_RDATA_PARITY => hbm_axi_rdata_parity(19),
            AXI_19_RDATA => hbm_axi_rdata(19),
            AXI_19_RID => hbm_axi_rid(19),
            AXI_19_RLAST => hbm_axi_rlast(19),
            AXI_19_RRESP => hbm_axi_rresp(19),
            AXI_19_RVALID => hbm_axi_rvalid(19),
            AXI_19_WREADY => hbm_axi_wready(19),
            AXI_19_BID => hbm_axi_bid(19),
            AXI_19_BRESP => hbm_axi_bresp(19),
            AXI_19_BVALID => hbm_axi_bvalid(19),
            AXI_20_ARREADY => hbm_axi_arready(20),
            AXI_20_AWREADY => hbm_axi_awready(20),
            AXI_20_RDATA_PARITY => hbm_axi_rdata_parity(20),
            AXI_20_RDATA => hbm_axi_rdata(20),
            AXI_20_RID => hbm_axi_rid(20),
            AXI_20_RLAST => hbm_axi_rlast(20),
            AXI_20_RRESP => hbm_axi_rresp(20),
            AXI_20_RVALID => hbm_axi_rvalid(20),
            AXI_20_WREADY => hbm_axi_wready(20),
            AXI_20_BID => hbm_axi_bid(20),
            AXI_20_BRESP => hbm_axi_bresp(20),
            AXI_20_BVALID => hbm_axi_bvalid(20),
            AXI_21_ARREADY => hbm_axi_arready(21),
            AXI_21_AWREADY => hbm_axi_awready(21),
            AXI_21_RDATA_PARITY => hbm_axi_rdata_parity(21),
            AXI_21_RDATA => hbm_axi_rdata(21),
            AXI_21_RID => hbm_axi_rid(21),
            AXI_21_RLAST => hbm_axi_rlast(21),
            AXI_21_RRESP => hbm_axi_rresp(21),
            AXI_21_RVALID => hbm_axi_rvalid(21),
            AXI_21_WREADY => hbm_axi_wready(21),
            AXI_21_BID => hbm_axi_bid(21),
            AXI_21_BRESP => hbm_axi_bresp(21),
            AXI_21_BVALID => hbm_axi_bvalid(21),
            AXI_22_ARREADY => hbm_axi_arready(22),
            AXI_22_AWREADY => hbm_axi_awready(22),
            AXI_22_RDATA_PARITY => hbm_axi_rdata_parity(22),
            AXI_22_RDATA => hbm_axi_rdata(22),
            AXI_22_RID => hbm_axi_rid(22),
            AXI_22_RLAST => hbm_axi_rlast(22),
            AXI_22_RRESP => hbm_axi_rresp(22),
            AXI_22_RVALID => hbm_axi_rvalid(22),
            AXI_22_WREADY => hbm_axi_wready(22),
            AXI_22_BID => hbm_axi_bid(22),
            AXI_22_BRESP => hbm_axi_bresp(22),
            AXI_22_BVALID => hbm_axi_bvalid(22),
            AXI_23_ARREADY => hbm_axi_arready(23),
            AXI_23_AWREADY => hbm_axi_awready(23),
            AXI_23_RDATA_PARITY => hbm_axi_rdata_parity(23),
            AXI_23_RDATA => hbm_axi_rdata(23),
            AXI_23_RID => hbm_axi_rid(23),
            AXI_23_RLAST => hbm_axi_rlast(23),
            AXI_23_RRESP => hbm_axi_rresp(23),
            AXI_23_RVALID => hbm_axi_rvalid(23),
            AXI_23_WREADY => hbm_axi_wready(23),
            AXI_23_BID => hbm_axi_bid(23),
            AXI_23_BRESP => hbm_axi_bresp(23),
            AXI_23_BVALID => hbm_axi_bvalid(23),
            AXI_24_ARREADY => hbm_axi_arready(24),
            AXI_24_AWREADY => hbm_axi_awready(24),
            AXI_24_RDATA_PARITY => hbm_axi_rdata_parity(24),
            AXI_24_RDATA => hbm_axi_rdata(24),
            AXI_24_RID => hbm_axi_rid(24),
            AXI_24_RLAST => hbm_axi_rlast(24),
            AXI_24_RRESP => hbm_axi_rresp(24),
            AXI_24_RVALID => hbm_axi_rvalid(24),
            AXI_24_WREADY => hbm_axi_wready(24),
            AXI_24_BID => hbm_axi_bid(24),
            AXI_24_BRESP => hbm_axi_bresp(24),
            AXI_24_BVALID => hbm_axi_bvalid(24),
            AXI_25_ARREADY => hbm_axi_arready(25),
            AXI_25_AWREADY => hbm_axi_awready(25),
            AXI_25_RDATA_PARITY => hbm_axi_rdata_parity(25),
            AXI_25_RDATA => hbm_axi_rdata(25),
            AXI_25_RID => hbm_axi_rid(25),
            AXI_25_RLAST => hbm_axi_rlast(25),
            AXI_25_RRESP => hbm_axi_rresp(25),
            AXI_25_RVALID => hbm_axi_rvalid(25),
            AXI_25_WREADY => hbm_axi_wready(25),
            AXI_25_BID => hbm_axi_bid(25),
            AXI_25_BRESP => hbm_axi_bresp(25),
            AXI_25_BVALID => hbm_axi_bvalid(25),
            AXI_26_ARREADY => hbm_axi_arready(26),
            AXI_26_AWREADY => hbm_axi_awready(26),
            AXI_26_RDATA_PARITY => hbm_axi_rdata_parity(26),
            AXI_26_RDATA => hbm_axi_rdata(26),
            AXI_26_RID => hbm_axi_rid(26),
            AXI_26_RLAST => hbm_axi_rlast(26),
            AXI_26_RRESP => hbm_axi_rresp(26),
            AXI_26_RVALID => hbm_axi_rvalid(26),
            AXI_26_WREADY => hbm_axi_wready(26),
            AXI_26_BID => hbm_axi_bid(26),
            AXI_26_BRESP => hbm_axi_bresp(26),
            AXI_26_BVALID => hbm_axi_bvalid(26),
            AXI_27_ARREADY => hbm_axi_arready(27),
            AXI_27_AWREADY => hbm_axi_awready(27),
            AXI_27_RDATA_PARITY => hbm_axi_rdata_parity(27),
            AXI_27_RDATA => hbm_axi_rdata(27),
            AXI_27_RID => hbm_axi_rid(27),
            AXI_27_RLAST => hbm_axi_rlast(27),
            AXI_27_RRESP => hbm_axi_rresp(27),
            AXI_27_RVALID => hbm_axi_rvalid(27),
            AXI_27_WREADY => hbm_axi_wready(27),
            AXI_27_BID => hbm_axi_bid(27),
            AXI_27_BRESP => hbm_axi_bresp(27),
            AXI_27_BVALID => hbm_axi_bvalid(27),
            AXI_28_ARREADY => hbm_axi_arready(28),
            AXI_28_AWREADY => hbm_axi_awready(28),
            AXI_28_RDATA_PARITY => hbm_axi_rdata_parity(28),
            AXI_28_RDATA => hbm_axi_rdata(28),
            AXI_28_RID => hbm_axi_rid(28),
            AXI_28_RLAST => hbm_axi_rlast(28),
            AXI_28_RRESP => hbm_axi_rresp(28),
            AXI_28_RVALID => hbm_axi_rvalid(28),
            AXI_28_WREADY => hbm_axi_wready(28),
            AXI_28_BID => hbm_axi_bid(28),
            AXI_28_BRESP => hbm_axi_bresp(28),
            AXI_28_BVALID => hbm_axi_bvalid(28),
            AXI_29_ARREADY => hbm_axi_arready(29),
            AXI_29_AWREADY => hbm_axi_awready(29),
            AXI_29_RDATA_PARITY => hbm_axi_rdata_parity(29),
            AXI_29_RDATA => hbm_axi_rdata(29),
            AXI_29_RID => hbm_axi_rid(29),
            AXI_29_RLAST => hbm_axi_rlast(29),
            AXI_29_RRESP => hbm_axi_rresp(29),
            AXI_29_RVALID => hbm_axi_rvalid(29),
            AXI_29_WREADY => hbm_axi_wready(29),
            AXI_29_BID => hbm_axi_bid(29),
            AXI_29_BRESP => hbm_axi_bresp(29),
            AXI_29_BVALID => hbm_axi_bvalid(29),
            AXI_30_ARREADY => hbm_axi_arready(30),
            AXI_30_AWREADY => hbm_axi_awready(30),
            AXI_30_RDATA_PARITY => hbm_axi_rdata_parity(30),
            AXI_30_RDATA => hbm_axi_rdata(30),
            AXI_30_RID => hbm_axi_rid(30),
            AXI_30_RLAST => hbm_axi_rlast(30),
            AXI_30_RRESP => hbm_axi_rresp(30),
            AXI_30_RVALID => hbm_axi_rvalid(30),
            AXI_30_WREADY => hbm_axi_wready(30),
            AXI_30_BID => hbm_axi_bid(30),
            AXI_30_BRESP => hbm_axi_bresp(30),
            AXI_30_BVALID => hbm_axi_bvalid(30),
            AXI_31_ARREADY => hbm_axi_arready(31),
            AXI_31_AWREADY => hbm_axi_awready(31),
            AXI_31_RDATA_PARITY => hbm_axi_rdata_parity(31),
            AXI_31_RDATA => hbm_axi_rdata(31),
            AXI_31_RID => hbm_axi_rid(31),
            AXI_31_RLAST => hbm_axi_rlast(31),
            AXI_31_RRESP => hbm_axi_rresp(31),
            AXI_31_RVALID => hbm_axi_rvalid(31),
            AXI_31_WREADY => hbm_axi_wready(31),
            AXI_31_BID => hbm_axi_bid(31),
            AXI_31_BRESP => hbm_axi_bresp(31),
            AXI_31_BVALID => hbm_axi_bvalid(31),
            apb_complete_0 => hbm_ready(0),
            apb_complete_1 => hbm_ready(1),
            DRAM_0_STAT_CATTRIP => hbm0_cattrip,
            DRAM_0_STAT_TEMP => open,
            DRAM_1_STAT_CATTRIP => hbm1_cattrip,
            DRAM_1_STAT_TEMP => open
        );
    else generate
        hbm_clk         <= '0';
        hbm_reset       <= '0';
        hbm_init_done   <= '0';
        hbm_axi_arready <= (others => '0');
        hbm_axi_rvalid  <= (others => '0');
        hbm_axi_awready <= (others => '0');
        hbm_axi_wready  <= (others => '0');
        hbm_axi_bvalid  <= (others => '0');
        HBM_CATTRIP     <= '0';
    end generate;

end architecture;
