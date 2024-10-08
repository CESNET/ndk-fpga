-- fpga.vhd: FB4CGG3 board top level entity and architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
library unisim;
library xpm;

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
    -- PCIe
    PCIE_SYSCLK_P       : in    std_logic;
    PCIE_SYSCLK_N       : in    std_logic;
    PCIE_SYSRST_N       : in    std_logic;
    PCIE_RX_P           : in    std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_RX_N           : in    std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_TX_P           : out   std_logic_vector(PCIE_LANES -1 downto 0);
    PCIE_TX_N           : out   std_logic_vector(PCIE_LANES -1 downto 0);

    -- 50 MHz external clock 
    REFCLK              : in    std_logic;

    -- Pulse per second
    PPS_IN              : in    std_logic;
    PPS_OUT             : out   std_logic;
    PPS_OUT_EN          : out   std_logic;

    -- SF2 SPI interface
    SF2_CLK             : out   std_logic;
    SF2_NSS             : out   std_logic;
    SF2_MOSI            : out   std_logic;
    SF2_MISO            : in    std_logic;
    SF2_INT             : in    std_logic;

    -- QSFP control
    QSFP0_SCL           : inout std_logic;
    QSFP0_SDA           : inout std_logic;
    QSFP0_LPMODE        : out   std_logic;
    QSFP0_RESET_N       : out   std_logic;
    QSFP0_MODPRS_N      : in    std_logic;
    QSFP0_INT_N         : in    std_logic;

    QSFP1_SCL           : inout std_logic;
    QSFP1_SDA           : inout std_logic;
    QSFP1_LPMODE        : out   std_logic;
    QSFP1_RESET_N       : out   std_logic;
    QSFP1_MODPRS_N      : in    std_logic;
    QSFP1_INT_N         : in    std_logic;

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

    -- Front (link status) LEDs SSR                     --TODO
    QLED_SDI            : out std_logic; -- Shift data
    QLED_LE             : out std_logic; -- Load
    QLED_CLK            : out std_logic;

    LED_STATUS          : out std_logic_vector(1 downto 0);

    -- DDR4A
    REFCLKA_DDR4_P  : in    std_logic;
    REFCLKA_DDR4_N  : in    std_logic;
    DDR4A_A         : out   std_logic_vector(16 downto 0);
    DDR4A_BA        : out   std_logic_vector(1 downto 0);
    DDR4A_CKE       : out   std_logic_vector(0 downto 0);
    DDR4A_CS_N      : out   std_logic_vector(0 downto 0);
    DDR4A_LDM       : inout std_logic_vector(4 downto 0);
    DDR4A_UDM       : inout std_logic_vector(3 downto 0);
    DDR4A_DQ        : inout std_logic_vector(71 downto 0);
    DDR4A_LDQS_N    : inout std_logic_vector(4 downto 0);
    DDR4A_LDQS_P    : inout std_logic_vector(4 downto 0);
    DDR4A_UDQS_N    : inout std_logic_vector(3 downto 0);
    DDR4A_UDQS_P    : inout std_logic_vector(3 downto 0);
    DDR4A_ODT       : out   std_logic_vector(0 downto 0);
    DDR4A_BG        : out   std_logic_vector(1 downto 0);
    DDR4A_RESET_N   : out   std_logic;
    DDR4A_ACT_N     : out   std_logic;
    DDR4A_CK_N      : out   std_logic_vector(0 downto 0);
    DDR4A_CK_P      : out   std_logic_vector(0 downto 0);

    -- DDR4B
    REFCLKB_DDR4_P : in     std_logic;
    REFCLKB_DDR4_N : in     std_logic;
    DDR4B_A       : out     std_logic_vector(16 downto 0);
    DDR4B_BA      : out     std_logic_vector(1 downto 0);
    DDR4B_CKE     : out     std_logic_vector(0 downto 0);
    DDR4B_CS_N    : out     std_logic_vector(0 downto 0);
    DDR4B_LDM     : inout   std_logic_vector(4 downto 0);
    DDR4B_UDM     : inout   std_logic_vector(3 downto 0);
    DDR4B_DQ      : inout   std_logic_vector(71 downto 0);
    DDR4B_LDQS_N  : inout   std_logic_vector(4 downto 0);
    DDR4B_LDQS_P  : inout   std_logic_vector(4 downto 0);
    DDR4B_UDQS_N  : inout   std_logic_vector(3 downto 0);
    DDR4B_UDQS_P  : inout   std_logic_vector(3 downto 0);
    DDR4B_ODT     : out     std_logic_vector(0 downto 0);
    DDR4B_BG      : out     std_logic_vector(1 downto 0);
    DDR4B_RESET_N : out     std_logic;
    DDR4B_ACT_N   : out     std_logic;
    DDR4B_CK_N    : out     std_logic_vector(0 downto 0);
    DDR4B_CK_P    : out     std_logic_vector(0 downto 0)

);
end entity;

architecture FULL of FPGA is

    constant PCIE_CLKS           : integer := 1;
    constant PCIE_CONS           : integer := 1;
    constant MISC_IN_WIDTH       : integer := 1+1+32+1+1+32;
    constant MISC_OUT_WIDTH      : integer := 1+1+1+1+1+4+8+32+1+1+4+8+32;
    constant ETH_LANES           : integer := 4;
    constant DMA_MODULES         : integer := PCIE_ENDPOINTS;
    constant DMA_ENDPOINTS       : integer := PCIE_ENDPOINTS;
    constant ETH_LANE_MAP        : integer_vector(2*ETH_LANES-1 downto 0) := (3, 2, 1, 0, 3, 2, 1, 0);
    constant ETH_LANE_RXPOLARITY : std_logic_vector(2*ETH_LANES-1 downto 0) := "00000000";
    constant ETH_LANE_TXPOLARITY : std_logic_vector(2*ETH_LANES-1 downto 0) := "00000000";
    constant DEVICE              : string  := "ULTRASCALE";

    -- DDR constants --
    constant DDR_PORTS           : integer := MEM_PORTS;
    constant DDR_ADDR_WIDTH      : integer := 29;
    constant DDR_BYTES           : integer := 9;
    --These values are IP core specific ... 
    constant DDR_AXI_ADDR_WIDTH  : integer := 32;
    constant DDR_AXI_DATA_WIDTH  : integer := 512;
    -- 1/4 of Memory Device interface Speed in Hz
    constant DDR_FREQ            : natural := 333333;
    -- Avalon constatnts --
    constant AMM_DATA_WIDTH         : integer := 512;
    constant AMM_BURST_COUNT_WIDTH  : integer := 8;
    constant AMM_ADDR_WIDTH         : integer := 26;
    constant REFR_PERIOD_WIDTH      : integer := 32;  
    
    signal sysclk_ibuf      : std_logic;
    signal sysclk_bufg      : std_logic;
    signal sysrst_cnt       : unsigned(4 downto 0) := (others => '0');
    signal sysrst           : std_logic := '1';

    signal eth_led_g        : std_logic_vector(2*4-1 downto 0);
    signal eth_led_r        : std_logic_vector(2*4-1 downto 0);
    
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
    
    signal misc_in          : std_logic_vector(MISC_IN_WIDTH-1 downto 0) := (others => '0');
    signal misc_out         : std_logic_vector(MISC_OUT_WIDTH-1 downto 0);

    signal pcie_clk         : std_logic;
    signal pcie_reset       : std_logic;

    signal boot_mi_clk      : std_logic;
    signal boot_mi_reset    : std_logic;
    signal boot_mi_dwr      : std_logic_vector(31 downto 0);
    signal boot_mi_addr     : std_logic_vector(31 downto 0);
    signal boot_mi_rd       : std_logic;
    signal boot_mi_wr       : std_logic;
    signal boot_mi_be       : std_logic_vector(3 downto 0);
    signal boot_mi_drd      : std_logic_vector(31 downto 0);
    signal boot_mi_ardy     : std_logic;
    signal boot_mi_drdy     : std_logic;

    -- Quad SPI controller
    signal axi_spi_clk      : std_logic;
    signal boot_reset       : std_logic;
    signal boot_clk         : std_logic;

    -- AXI Flash Controller 
    signal axi_mi_addr_s    : std_logic_vector(8 - 1 downto 0);           
    signal axi_mi_dwr_s     : std_logic_vector(32 - 1 downto 0);         
    signal axi_mi_wr_s      : std_logic;        
    signal axi_mi_rd_s      : std_logic;        
    signal axi_mi_be_s      : std_logic_vector((32/8)-1 downto 0);        
    signal axi_mi_ardy_s    : std_logic;          
    signal axi_mi_drd_s     : std_logic_vector(32 - 1 downto 0);         
    signal axi_mi_drdy_s    : std_logic;

    --BMC controller 
    signal bmc_mi_addr_s    : std_logic_vector(8 - 1 downto 0);
    signal bmc_mi_dwr_s     : std_logic_vector(32 - 1 downto 0);
    signal bmc_mi_wr_s      : std_logic;
    signal bmc_mi_rd_s      : std_logic;
    signal bmc_mi_be_s      : std_logic_vector(3 downto 0);
    signal bmc_mi_ardy_s    : std_logic;
    signal bmc_mi_drd_s     : std_logic_vector(32 - 1 downto 0);
    signal bmc_mi_drdy_s    : std_logic;

    -- DDR AXI signals
    signal ddr_areset                   : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_awid               : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0);
    signal ddr_s_axi_awaddr             : slv_array_t     (DDR_PORTS-1 downto 0)(DDR_AXI_ADDR_WIDTH-1 DOWNTO 0);
    signal ddr_s_axi_awlen              : slv_array_t     (DDR_PORTS-1 downto 0)(7 DOWNTO 0);
    signal ddr_s_axi_awsize             : slv_array_t     (DDR_PORTS-1 downto 0)(2 DOWNTO 0);
    signal ddr_s_axi_awburst            : slv_array_t     (DDR_PORTS-1 downto 0)(1 DOWNTO 0);
    signal ddr_s_axi_awlock             : slv_array_t     (DDR_PORTS-1 downto 0)(0 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_awcache            : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_awprot             : slv_array_t     (DDR_PORTS-1 downto 0)(2 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_awqos              : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_awvalid            : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_awready            : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_wdata              : slv_array_t     (DDR_PORTS-1 downto 0)(DDR_AXI_DATA_WIDTH-1 DOWNTO 0);
    signal ddr_s_axi_wstrb              : slv_array_t     (DDR_PORTS-1 downto 0)(DDR_AXI_DATA_WIDTH/8-1 DOWNTO 0);
    signal ddr_s_axi_wlast              : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_wvalid             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_wready             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_bready             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_bid                : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0);
    signal ddr_s_axi_bresp              : slv_array_t     (DDR_PORTS-1 downto 0)(1 DOWNTO 0);
    signal ddr_s_axi_bvalid             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_arid               : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0);
    signal ddr_s_axi_araddr             : slv_array_t     (DDR_PORTS-1 downto 0)(DDR_AXI_ADDR_WIDTH-1 DOWNTO 0);
    signal ddr_s_axi_arlen              : slv_array_t     (DDR_PORTS-1 downto 0)(7 DOWNTO 0);
    signal ddr_s_axi_arsize             : slv_array_t     (DDR_PORTS-1 downto 0)(2 DOWNTO 0);
    signal ddr_s_axi_arburst            : slv_array_t     (DDR_PORTS-1 downto 0)(1 DOWNTO 0);
    signal ddr_s_axi_arcache            : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_arlock             : slv_array_t     (DDR_PORTS-1 downto 0)(0 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_arprot             : slv_array_t     (DDR_PORTS-1 downto 0)(2 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_arqos              : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0):=(others=>(others => '0'));
    signal ddr_s_axi_arvalid            : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_arready            : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_rready             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_rlast              : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_rvalid             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_s_axi_rresp              : slv_array_t     (DDR_PORTS-1 downto 0)(1 DOWNTO 0);
    signal ddr_s_axi_rid                : slv_array_t     (DDR_PORTS-1 downto 0)(3 DOWNTO 0);
    signal ddr_s_axi_rdata              : slv_array_t     (DDR_PORTS-1 downto 0)(DDR_AXI_DATA_WIDTH-1 DOWNTO 0);
    
    -- DDR4A interface
    signal ddr4a_rst        : std_logic;
    signal ddr4a_app_hi_pri : std_logic;
    signal ddr4a_dqs_p      : std_logic_vector(DDR_BYTES-1 downto 0);
    signal ddr4a_dqs_n      : std_logic_vector(DDR_BYTES-1 downto 0);
    signal ddr4a_dm         : std_logic_vector(DDR_BYTES-1 downto 0);

    -- DDR4B interface
    signal ddr4b_rst        : std_logic;
    signal ddr4b_app_hi_pri : std_logic;
    signal ddr4b_dqs_p      : std_logic_vector(DDR_BYTES-1 downto 0);
    signal ddr4b_dqs_n      : std_logic_vector(DDR_BYTES-1 downto 0);
    signal ddr4b_dm         : std_logic_vector(DDR_BYTES-1 downto 0); 

    -- MEM_TESTER signals
    signal mem_clk                  : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_rst                  : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_avmm_ready           : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_avmm_read            : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_avmm_write           : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_avmm_address         : slv_array_t(DDR_PORTS-1 downto 0)(AMM_ADDR_WIDTH - 1 downto 0);
    signal mem_avmm_burstcount      : slv_array_t(DDR_PORTS-1 downto 0)(AMM_BURST_COUNT_WIDTH - 1 downto 0);
    signal mem_avmm_writedata       : slv_array_t(DDR_PORTS-1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal mem_avmm_readdata        : slv_array_t(DDR_PORTS-1 downto 0)(AMM_DATA_WIDTH - 1 downto 0);
    signal mem_avmm_readdatavalid   : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_refr_period          : slv_array_t(DDR_PORTS-1 downto 0)(REFR_PERIOD_WIDTH - 1 downto 0);
    signal mem_refr_req             : std_logic_vector(DDR_PORTS -1 downto 0);
    signal mem_refr_ack             : std_logic_vector(DDR_PORTS -1 downto 0);
    signal emif_rst_req             : std_logic_vector(DDR_PORTS -1 downto 0);
    signal emif_rst_done            : std_logic_vector(DDR_PORTS -1 downto 0);
    signal emif_ecc_usr_int         : std_logic_vector(DDR_PORTS -1 downto 0);
    signal emif_cal_success         : std_logic_vector(DDR_PORTS -1 downto 0);
    signal emif_cal_fail            : std_logic_vector(DDR_PORTS -1 downto 0);

    -- DDR signals
    signal ddr_init_calib_complete      : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_ui_clk                   : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_ui_clk_sync_rst          : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_en                   : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_hi_pri               : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_wdf_end              : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_wdf_wren             : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_rd_data_end          : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_rd_data_valid        : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_rdy                  : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_wdf_rdy              : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_app_addr                 : std_logic_vector(DDR_PORTS*DDR_ADDR_WIDTH-1 downto 0);
    signal ddr_app_cmd                  : std_logic_vector(DDR_PORTS*3-1 downto 0);
    signal ddr_app_wdf_data             : std_logic_vector(DDR_PORTS*DDR_BYTES*64-1 downto 0);
    signal ddr_app_wdf_mask             : std_logic_vector(DDR_PORTS*DDR_BYTES*8-1 downto 0);
    signal ddr_app_rd_data              : std_logic_vector(DDR_PORTS*DDR_BYTES*64-1 downto 0);
    signal ddr_rst                      : std_logic_vector(DDR_PORTS-1 downto 0);
    signal ddr_dqs_p                    : std_logic_vector(DDR_PORTS*DDR_BYTES-1 downto 0);
    signal ddr_dqs_n                    : std_logic_vector(DDR_PORTS*DDR_BYTES-1 downto 0);
    signal ddr_dm                       : std_logic_vector(DDR_PORTS*DDR_BYTES-1 downto 0);
    
    -- DDR IP core with AXI4 interface
    component DDR4_AXI
        port (
            c0_init_calib_complete      : out   std_logic;
            c0_sys_clk_p                : in    std_logic;
            c0_sys_clk_n                : in    std_logic;
            c0_ddr4_adr                 : out   std_logic_vector(16 downto 0);
            c0_ddr4_ba                  : out   std_logic_vector(1 downto 0);
            c0_ddr4_cke                 : out   std_logic_vector(0 downto 0);
            c0_ddr4_cs_n                : out   std_logic_vector(0 downto 0);
            c0_ddr4_dm_dbi_n            : inout std_logic_vector(8 downto 0);
            c0_ddr4_dq                  : inout std_logic_vector(71 downto 0);
            c0_ddr4_dqs_c               : inout std_logic_vector(8 downto 0);
            c0_ddr4_dqs_t               : inout std_logic_vector(8 downto 0);
            c0_ddr4_odt                 : out   std_logic_vector(0 downto 0);
            c0_ddr4_bg                  : out   std_logic;
            c0_ddr4_reset_n             : out   std_logic;
            c0_ddr4_act_n               : out   std_logic;
            c0_ddr4_ck_c                : out   std_logic_vector(0 downto 0);
            c0_ddr4_ck_t                : out   std_logic_vector(0 downto 0);
            c0_ddr4_ui_clk              : out   std_logic;
            c0_ddr4_ui_clk_sync_rst     : out   std_logic;
            c0_ddr4_aresetn             : in    std_logic;
            c0_ddr4_s_axi_awid          : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_awaddr        : in    std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_awlen         : in    std_logic_vector(7 downto 0);
            c0_ddr4_s_axi_awsize        : in    std_logic_vector(2 downto 0);
            c0_ddr4_s_axi_awburst       : in    std_logic_vector(1 downto 0);
            c0_ddr4_s_axi_awlock        : in    std_logic_vector(0 downto 0);
            c0_ddr4_s_axi_awcache       : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_awprot        : in    std_logic_vector(2 downto 0);
            c0_ddr4_s_axi_awqos         : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_awvalid       : in    std_logic;
            c0_ddr4_s_axi_awready       : out   std_logic;
            c0_ddr4_s_axi_wdata         : in    std_logic_vector(511 downto 0);
            c0_ddr4_s_axi_wstrb         : in    std_logic_vector(63 downto 0);
            c0_ddr4_s_axi_wlast         : in    std_logic;
            c0_ddr4_s_axi_wvalid        : in    std_logic;
            c0_ddr4_s_axi_wready        : out   std_logic;
            c0_ddr4_s_axi_bready        : in    std_logic;
            c0_ddr4_s_axi_bid           : out   std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_bresp         : out   std_logic_vector(1 downto 0);
            c0_ddr4_s_axi_bvalid        : out   std_logic;
            c0_ddr4_s_axi_arid          : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_araddr        : in    std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_arlen         : in    std_logic_vector(7 downto 0);
            c0_ddr4_s_axi_arsize        : in    std_logic_vector(2 downto 0);
            c0_ddr4_s_axi_arburst       : in    std_logic_vector(1 downto 0);
            c0_ddr4_s_axi_arlock        : in    std_logic_vector(0 downto 0);
            c0_ddr4_s_axi_arcache       : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_arprot        : in    std_logic_vector(2 downto 0);
            c0_ddr4_s_axi_arqos         : in    std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_arvalid       : in    std_logic;
            c0_ddr4_s_axi_arready       : out   std_logic;
            c0_ddr4_s_axi_rready        : in    std_logic;
            c0_ddr4_s_axi_rlast         : out   std_logic;
            c0_ddr4_s_axi_rvalid        : out   std_logic;
            c0_ddr4_s_axi_rresp         : out   std_logic_vector(1 downto 0);
            c0_ddr4_s_axi_rid           : out   std_logic_vector(3 downto 0);
            c0_ddr4_s_axi_rdata         : out   std_logic_vector(511 downto 0);
            sys_rst                     : in    std_logic;
            --------------
            ---ECC_CTRL---
            --------------
            dbg_clk                     : out   std_logic;
            dbg_bus                     : out   std_logic_vector(511 downto 0);
            c0_ddr4_interrupt           : out   std_logic;
            c0_ddr4_s_axi_ctrl_awvalid  : in    std_logic;
            c0_ddr4_s_axi_ctrl_awready  : out   std_logic;
            c0_ddr4_s_axi_ctrl_awaddr   : in    std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_ctrl_wvalid   : in    std_logic;
            c0_ddr4_s_axi_ctrl_wready   : out   std_logic;
            c0_ddr4_s_axi_ctrl_wdata    : in    std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_ctrl_bvalid   : out   std_logic;
            c0_ddr4_s_axi_ctrl_bready   : in    std_logic;
            c0_ddr4_s_axi_ctrl_bresp    : out   std_logic_vector(1 downto 0);
            c0_ddr4_s_axi_ctrl_arvalid  : in    std_logic;
            c0_ddr4_s_axi_ctrl_arready  : out   std_logic;
            c0_ddr4_s_axi_ctrl_araddr   : in    std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_ctrl_rvalid   : out   std_logic;
            c0_ddr4_s_axi_ctrl_rready   : in    std_logic;
            c0_ddr4_s_axi_ctrl_rdata    : out   std_logic_vector(31 downto 0);
            c0_ddr4_s_axi_ctrl_rresp    : out   std_logic_vector(1 downto 0)
            
            );
        end component;

begin

    -- DDR IMPLEMENTATION ------------------------------------------------------
    ddr4a_en_g : if DDR_PORTS >= 1 generate
        ddr4a_rst           <= sysrst;
        DDR4A_BG(1)         <= '0';

        ddr4a_mapping_g : for i in 0 to (DDR_BYTES/2-1) generate
            ddr4a_dqs_p(i*2)      <= DDR4A_LDQS_P(i);
            ddr4a_dqs_n(i*2)      <= DDR4A_LDQS_N(i);
            ddr4a_dm(i*2)         <= DDR4A_LDM(i);

            ddr4a_dqs_p(i*2+1)    <= DDR4A_UDQS_P(i);
            ddr4a_dqs_n(i*2+1)    <= DDR4A_UDQS_N(i);
            ddr4a_dm(i*2+1)       <= DDR4A_UDM(i);
        end generate;
        
        -- FB2CGHH specific (DDR_BYTES=9)
        ddr4a_dqs_n(DDR_BYTES-1)    <= DDR4A_LDQS_N((DDR_BYTES/2));
        ddr4a_dqs_p(DDR_BYTES-1)    <= DDR4A_LDQS_P((DDR_BYTES/2));
        ddr4a_dm(DDR_BYTES-1)       <= DDR4A_LDM((DDR_BYTES/2));
        --

        ddr4a_axi_i : DDR4_AXI
        port map (
            c0_sys_clk_p            => REFCLKA_DDR4_P,
            c0_sys_clk_n            => REFCLKA_DDR4_N,
            c0_ddr4_adr             => DDR4A_A,
            c0_ddr4_ba              => DDR4A_BA,
            c0_ddr4_cke             => DDR4A_CKE(0 downto 0),
            c0_ddr4_cs_n            => DDR4A_CS_N(0 downto 0),
            c0_ddr4_dq              => DDR4A_DQ(DDR_BYTES*8-1 downto 0),
            c0_ddr4_odt             => DDR4A_ODT(0 downto 0),
            c0_ddr4_bg              => DDR4A_BG(0),
            c0_ddr4_reset_n         => DDR4A_RESET_N,
            c0_ddr4_act_n           => DDR4A_ACT_N,
            c0_ddr4_ck_c            => DDR4A_CK_N(0 downto 0),
            c0_ddr4_ck_t            => DDR4A_CK_P(0 downto 0),
            c0_ddr4_dm_dbi_n        => ddr4a_dm(DDR_BYTES-1 downto 0),
            c0_ddr4_dqs_c           => ddr4a_dqs_n(DDR_BYTES-1 downto 0),
            c0_ddr4_dqs_t           => ddr4a_dqs_p(DDR_BYTES-1 downto 0),
            sys_rst                 => ddr4a_rst,
            c0_init_calib_complete  => ddr_init_calib_complete(0),
            c0_ddr4_ui_clk          => ddr_ui_clk(0),
            c0_ddr4_ui_clk_sync_rst => ddr_ui_clk_sync_rst(0),
            c0_ddr4_aresetn         => not ddr_areset(0),
            c0_ddr4_s_axi_awid      => ddr_s_axi_awid(0),
            c0_ddr4_s_axi_awaddr    => ddr_s_axi_awaddr(0),
            c0_ddr4_s_axi_awlen     => ddr_s_axi_awlen(0),
            c0_ddr4_s_axi_awsize    => ddr_s_axi_awsize(0),
            c0_ddr4_s_axi_awburst   => ddr_s_axi_awburst(0),
            c0_ddr4_s_axi_awlock    => ddr_s_axi_awlock(0),
            c0_ddr4_s_axi_awcache   => ddr_s_axi_awcache(0),
            c0_ddr4_s_axi_awprot    => ddr_s_axi_awprot(0),
            c0_ddr4_s_axi_awqos     => ddr_s_axi_awqos(0),
            c0_ddr4_s_axi_awvalid   => ddr_s_axi_awvalid(0),
            c0_ddr4_s_axi_awready   => ddr_s_axi_awready(0),
            c0_ddr4_s_axi_wdata     => ddr_s_axi_wdata(0),
            c0_ddr4_s_axi_wstrb     => ddr_s_axi_wstrb(0),
            c0_ddr4_s_axi_wlast     => ddr_s_axi_wlast(0),
            c0_ddr4_s_axi_wvalid    => ddr_s_axi_wvalid(0),
            c0_ddr4_s_axi_wready    => ddr_s_axi_wready(0),
            c0_ddr4_s_axi_bready    => ddr_s_axi_bready(0),
            c0_ddr4_s_axi_bid       => ddr_s_axi_bid(0),
            c0_ddr4_s_axi_bresp     => ddr_s_axi_bresp(0),
            c0_ddr4_s_axi_bvalid    => ddr_s_axi_bvalid(0),
            c0_ddr4_s_axi_arid      => ddr_s_axi_arid(0),
            c0_ddr4_s_axi_araddr    => ddr_s_axi_araddr(0),
            c0_ddr4_s_axi_arlen     => ddr_s_axi_arlen(0),
            c0_ddr4_s_axi_arsize    => ddr_s_axi_arsize(0),
            c0_ddr4_s_axi_arburst   => ddr_s_axi_arburst(0),
            c0_ddr4_s_axi_arlock    => ddr_s_axi_arlock(0),
            c0_ddr4_s_axi_arcache   => ddr_s_axi_arcache(0),
            c0_ddr4_s_axi_arprot    => ddr_s_axi_arprot(0),
            c0_ddr4_s_axi_arqos     => ddr_s_axi_arqos(0),
            c0_ddr4_s_axi_arvalid   => ddr_s_axi_arvalid(0),
            c0_ddr4_s_axi_arready   => ddr_s_axi_arready(0),
            c0_ddr4_s_axi_rready    => ddr_s_axi_rready(0),
            c0_ddr4_s_axi_rlast     => ddr_s_axi_rlast(0),
            c0_ddr4_s_axi_rvalid    => ddr_s_axi_rvalid(0),
            c0_ddr4_s_axi_rresp     => ddr_s_axi_rresp(0),
            c0_ddr4_s_axi_rid       => ddr_s_axi_rid(0),
            c0_ddr4_s_axi_rdata     => ddr_s_axi_rdata(0),
            --------------
            ---ECC_CTRL---
            --------------
            dbg_clk                     => open,
            dbg_bus                     => open,
            c0_ddr4_interrupt           => open,
            c0_ddr4_s_axi_ctrl_awready  => open,
            c0_ddr4_s_axi_ctrl_wready   => open,
            c0_ddr4_s_axi_ctrl_bvalid   => open,
            c0_ddr4_s_axi_ctrl_bresp    => open,
            c0_ddr4_s_axi_ctrl_arready  => open,
            c0_ddr4_s_axi_ctrl_rvalid   => open,
            c0_ddr4_s_axi_ctrl_rdata    => open,
            c0_ddr4_s_axi_ctrl_rresp    => open,
            c0_ddr4_s_axi_ctrl_awvalid  => '0',
            c0_ddr4_s_axi_ctrl_wvalid   => '0',
            c0_ddr4_s_axi_ctrl_bready   => '0',
            c0_ddr4_s_axi_ctrl_arvalid  => '0',
            c0_ddr4_s_axi_ctrl_rready   => '0',
            c0_ddr4_s_axi_ctrl_awaddr   => (others => '0'),
            c0_ddr4_s_axi_ctrl_wdata    => (others => '0'),
            c0_ddr4_s_axi_ctrl_araddr   => (others => '0')
        );

    else generate
        ddr_init_calib_complete(0)                  <= '0';
        DDR4A_A                                     <= (others => '0');
        DDR4A_BA                                    <= (others => '0');
        DDR4A_CKE(0 downto 0)                       <= (others => '0');
        DDR4A_CS_N(0 downto 0)                      <= (others => '1');
        DDR4A_LDM(((DDR_BYTES/2)+1)-1 downto 0)     <= (others => '0');
        DDR4A_DQ((DDR_BYTES*8)-1 downto 0)          <= (others => '0');
        DDR4A_UDM((DDR_BYTES/2)-1 downto 0)         <= (others => '0');
        DDR4A_ODT(0 downto 0)                       <= (others => '1');
        DDR4A_BG                                    <= (others => '0');
        DDR4A_RESET_N                               <= '0';
        DDR4A_ACT_N                                 <= '0';

        -- Insert differential buffers
        CK_BUF: OBUFDS 
        port map (
            I   => '1', 
            O   => DDR4A_CK_P(0), 
            OB  => DDR4A_CK_N(0)
        );

        ldqs_buf_g: for p in 0 to ((DDR_BYTES/2)+1)-1 generate
            LDQS_BUF: IOBUFDS 
            port map (
                O   => open, 
                I   => '0', 
                T   => '0', 
                IO  => DDR4A_LDQS_P(p), 
                IOB => DDR4A_LDQS_N(p)
            );
        end generate;

        udqs_buf_g: for p in 0 to (DDR_BYTES/2)-1 generate
            UDQS_BUF: IOBUFDS 
            port map (
                O   => open, 
                I   => '0', 
                T   => '0', 
                IO  => DDR4A_UDQS_P(p),
                IOB => DDR4A_UDQS_N(p)
            );
        end generate;

    end generate; 

    ddr4b_en_g : if DDR_PORTS >= 2 generate
        ddr4b_rst           <= sysrst;
        DDR4B_BG(1)         <= '0';

        ddr4b_mapping_g : for i in 0 to (DDR_BYTES/2-1) generate
            ddr4b_dqs_p(i*2)      <= DDR4B_LDQS_P(i);
            ddr4b_dqs_n(i*2)      <= DDR4B_LDQS_N(i);
            ddr4b_dm(i*2)         <= DDR4B_LDM(i);

            ddr4b_dqs_p(i*2+1)    <= DDR4B_UDQS_P(i);
            ddr4b_dqs_n(i*2+1)    <= DDR4B_UDQS_N(i);
            ddr4b_dm(i*2+1)       <= DDR4B_UDM(i);
        end generate;
        
        -- FB2CGHH specific (DDR_BYTES=9)
        ddr4b_dqs_n(DDR_BYTES-1)    <= DDR4B_LDQS_N((DDR_BYTES/2));
        ddr4b_dqs_p(DDR_BYTES-1)    <= DDR4B_LDQS_P((DDR_BYTES/2));
        ddr4b_dm(DDR_BYTES-1)       <= DDR4B_LDM((DDR_BYTES/2));
        --

        ddr4_axi_i : DDR4_AXI
        port map (
            c0_sys_clk_p            => REFCLKB_DDR4_P,
            c0_sys_clk_n            => REFCLKB_DDR4_N,
            c0_ddr4_adr             => DDR4B_A,
            c0_ddr4_ba              => DDR4B_BA,
            c0_ddr4_cke             => DDR4B_CKE(0 downto 0),
            c0_ddr4_cs_n            => DDR4B_CS_N(0 downto 0),
            c0_ddr4_dq              => DDR4B_DQ(DDR_BYTES*8-1 downto 0),
            c0_ddr4_odt             => DDR4B_ODT(0 downto 0),
            c0_ddr4_bg              => DDR4B_BG(0),
            c0_ddr4_reset_n         => DDR4B_RESET_N,
            c0_ddr4_act_n           => DDR4B_ACT_N,
            c0_ddr4_ck_c            => DDR4B_CK_N(0 downto 0),
            c0_ddr4_ck_t            => DDR4B_CK_P(0 downto 0),
            c0_ddr4_dm_dbi_n        => ddr4b_dm(DDR_BYTES-1 downto 0),
            c0_ddr4_dqs_c           => ddr4b_dqs_n(DDR_BYTES-1 downto 0),
            c0_ddr4_dqs_t           => ddr4b_dqs_p(DDR_BYTES-1 downto 0),
            sys_rst                 => ddr4b_rst,
            c0_init_calib_complete  => ddr_init_calib_complete(1),
            c0_ddr4_ui_clk          => ddr_ui_clk(1),
            c0_ddr4_ui_clk_sync_rst => ddr_ui_clk_sync_rst(1),
            c0_ddr4_aresetn         => not ddr_areset(1),
            c0_ddr4_s_axi_awid      => ddr_s_axi_awid(1),
            c0_ddr4_s_axi_awaddr    => ddr_s_axi_awaddr(1),
            c0_ddr4_s_axi_awlen     => ddr_s_axi_awlen(1),
            c0_ddr4_s_axi_awsize    => ddr_s_axi_awsize(1),
            c0_ddr4_s_axi_awburst   => ddr_s_axi_awburst(1),
            c0_ddr4_s_axi_awlock    => ddr_s_axi_awlock(1),
            c0_ddr4_s_axi_awcache   => ddr_s_axi_awcache(1),
            c0_ddr4_s_axi_awprot    => ddr_s_axi_awprot(1),
            c0_ddr4_s_axi_awqos     => ddr_s_axi_awqos(1),
            c0_ddr4_s_axi_awvalid   => ddr_s_axi_awvalid(1),
            c0_ddr4_s_axi_awready   => ddr_s_axi_awready(1),
            c0_ddr4_s_axi_wdata     => ddr_s_axi_wdata(1),
            c0_ddr4_s_axi_wstrb     => ddr_s_axi_wstrb(1),
            c0_ddr4_s_axi_wlast     => ddr_s_axi_wlast(1),
            c0_ddr4_s_axi_wvalid    => ddr_s_axi_wvalid(1),
            c0_ddr4_s_axi_wready    => ddr_s_axi_wready(1),
            c0_ddr4_s_axi_bready    => ddr_s_axi_bready(1),
            c0_ddr4_s_axi_bid       => ddr_s_axi_bid(1),
            c0_ddr4_s_axi_bresp     => ddr_s_axi_bresp(1),
            c0_ddr4_s_axi_bvalid    => ddr_s_axi_bvalid(1),
            c0_ddr4_s_axi_arid      => ddr_s_axi_arid(1),
            c0_ddr4_s_axi_araddr    => ddr_s_axi_araddr(1),
            c0_ddr4_s_axi_arlen     => ddr_s_axi_arlen(1),
            c0_ddr4_s_axi_arsize    => ddr_s_axi_arsize(1),
            c0_ddr4_s_axi_arburst   => ddr_s_axi_arburst(1),
            c0_ddr4_s_axi_arlock    => ddr_s_axi_arlock(1),
            c0_ddr4_s_axi_arcache   => ddr_s_axi_arcache(1),
            c0_ddr4_s_axi_arprot    => ddr_s_axi_arprot(1),
            c0_ddr4_s_axi_arqos     => ddr_s_axi_arqos(1),
            c0_ddr4_s_axi_arvalid   => ddr_s_axi_arvalid(1),
            c0_ddr4_s_axi_arready   => ddr_s_axi_arready(1),
            c0_ddr4_s_axi_rready    => ddr_s_axi_rready(1),
            c0_ddr4_s_axi_rlast     => ddr_s_axi_rlast(1),
            c0_ddr4_s_axi_rvalid    => ddr_s_axi_rvalid(1),
            c0_ddr4_s_axi_rresp     => ddr_s_axi_rresp(1),
            c0_ddr4_s_axi_rid       => ddr_s_axi_rid(1),
            c0_ddr4_s_axi_rdata     => ddr_s_axi_rdata(1),
            --------------
            ---ECC_CTRL---
            --------------
            dbg_clk                     => open,
            dbg_bus                     => open,
            c0_ddr4_interrupt           => open,
            c0_ddr4_s_axi_ctrl_awready  => open,
            c0_ddr4_s_axi_ctrl_wready   => open,
            c0_ddr4_s_axi_ctrl_bvalid   => open,
            c0_ddr4_s_axi_ctrl_bresp    => open,
            c0_ddr4_s_axi_ctrl_arready  => open,
            c0_ddr4_s_axi_ctrl_rvalid   => open,
            c0_ddr4_s_axi_ctrl_rdata    => open,
            c0_ddr4_s_axi_ctrl_rresp    => open,
            c0_ddr4_s_axi_ctrl_awvalid  => '0',
            c0_ddr4_s_axi_ctrl_wvalid   => '0',
            c0_ddr4_s_axi_ctrl_bready   => '0',
            c0_ddr4_s_axi_ctrl_arvalid  => '0',
            c0_ddr4_s_axi_ctrl_rready   => '0',
            c0_ddr4_s_axi_ctrl_awaddr   => (others => '0'),
            c0_ddr4_s_axi_ctrl_wdata    => (others => '0'),
            c0_ddr4_s_axi_ctrl_araddr   => (others => '0')
        );

    else generate
        ddr_init_calib_complete(0)                  <= '0';
        DDR4B_A                                     <= (others => '0');
        DDR4B_BA                                    <= (others => '0');
        DDR4B_CKE(0 downto 0)                       <= (others => '0');
        DDR4B_CS_N(0 downto 0)                      <= (others => '1');
        DDR4B_LDM(((DDR_BYTES/2)+1)-1 downto 0)     <= (others => '0');
        DDR4B_DQ((DDR_BYTES*8)-1 downto 0)          <= (others => '0');
        DDR4B_UDM((DDR_BYTES/2)-1 downto 0)         <= (others => '0');
        DDR4B_ODT(0 downto 0)                       <= (others => '1');
        DDR4B_BG                                    <= (others => '0');
        DDR4B_RESET_N                               <= '0';
        DDR4B_ACT_N                                 <= '0';

        -- Insert differential buffers
        CK_BUF: OBUFDS 
        port map (
            I   => '1', 
            O   => DDR4B_CK_P(0), 
            OB  => DDR4B_CK_N(0)
        );

        ldqs_buf_g: for p in 0 to ((DDR_BYTES/2)+1)-1 generate
            LDQS_BUF: IOBUFDS 
            port map (
                O   => open, 
                I   => '0', 
                T   => '0', 
                IO  => DDR4B_LDQS_P(p), 
                IOB => DDR4B_LDQS_N(p)
            );
        end generate;

        udqs_buf_g: for p in 0 to (DDR_BYTES/2)-1 generate
            UDQS_BUF: IOBUFDS 
            port map (
                O   => open, 
                I   => '0', 
                T   => '0', 
                IO  => DDR4B_UDQS_P(p),
                IOB => DDR4B_UDQS_N(p)
            );
        end generate;

    end generate;         

    ddr4bridge_g : for i in DDR_PORTS -1 downto 0 generate
        ddr4bridge_i : entity work.AXI2AVMM_BRIDGE
        port map(
            MEM_CLK                 => ddr_ui_clk(i),
            MEM_RST                 => ddr_ui_clk_sync_rst(i),
                
            -- DDR4_AXI interface
            DDR_S_AXI_AWID          => ddr_s_axi_awid(i),
            DDR_S_AXI_AWADDR        => ddr_s_axi_awaddr(i),
            DDR_S_AXI_AWLEN         => ddr_s_axi_awlen(i),
            DDR_S_AXI_AWSIZE        => ddr_s_axi_awsize(i),
            DDR_S_AXI_AWBURST       => ddr_s_axi_awburst(i),
            DDR_S_AXI_AWVALID       => ddr_s_axi_awvalid(i),
            DDR_S_AXI_AWREADY       => ddr_s_axi_awready(i),
            DDR_S_AXI_WDATA         => ddr_s_axi_wdata(i),
            DDR_S_AXI_WSTRB         => ddr_s_axi_wstrb(i),
            DDR_S_AXI_WLAST         => ddr_s_axi_wlast(i),
            DDR_S_AXI_WVALID        => ddr_s_axi_wvalid(i),
            DDR_S_AXI_WREADY        => ddr_s_axi_wready(i),
            DDR_S_AXI_BREADY        => ddr_s_axi_bready(i),
            DDR_S_AXI_BID           => ddr_s_axi_bid(i),
            DDR_S_AXI_BRESP         => ddr_s_axi_bresp(i),
            DDR_S_AXI_BVALID        => ddr_s_axi_bvalid(i),
            DDR_S_AXI_ARID          => ddr_s_axi_arid(i),
            DDR_S_AXI_ARADDR        => ddr_s_axi_araddr(i),
            DDR_S_AXI_ARLEN         => ddr_s_axi_arlen(i),
            DDR_S_AXI_ARSIZE        => ddr_s_axi_arsize(i),
            DDR_S_AXI_ARBURST       => ddr_s_axi_arburst(i),
            DDR_S_AXI_ARVALID       => ddr_s_axi_arvalid(i),
            DDR_S_AXI_ARREADY       => ddr_s_axi_arready(i),
            DDR_S_AXI_RREADY        => ddr_s_axi_rready(i),
            DDR_S_AXI_RVALID        => ddr_s_axi_rvalid(i),
            DDR_S_AXI_RLAST         => ddr_s_axi_rlast(i),
            DDR_S_AXI_RRESP         => ddr_s_axi_rresp(i),
            DDR_S_AXI_RID           => ddr_s_axi_rid(i),
            DDR_S_AXI_RDATA         => ddr_s_axi_rdata(i),
        
            -- EMIF interface
            AMM_READY               => mem_avmm_ready(i),
            AMM_READ                => mem_avmm_read(i),
            AMM_WRITE               => mem_avmm_write(i),
            AMM_ADDRESS             => mem_avmm_address(i),
            AMM_BURST_COUNT         => mem_avmm_burstcount(i),
            AMM_WRITE_DATA          => mem_avmm_writedata(i),
            AMM_READ_DATA           => mem_avmm_readdata(i),
            AMM_READ_DATA_VALID     => mem_avmm_readdatavalid(i)
        );
    end generate;

    sysclk_ibuf_i : IBUFG
    port map (
        I  => REFCLK,
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

    PPS_OUT <= PPS_IN;

    -- QSFP MAPPING ------------------------------------------------------------
    eth_refclk_p <= QSFP1_REFCLK_P & QSFP0_REFCLK_P; 
    eth_refclk_n <= QSFP1_REFCLK_N & QSFP0_REFCLK_N;

    eth_rx_p <= QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP1_RX_N & QSFP0_RX_N;


    QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);


    QSFP1_LPMODE  <= qsfp_lpmode(1);
    QSFP1_RESET_N <= qsfp_reset_n(1);
    QSFP1_SCL     <= qsfp_scl(1);
    QSFP1_SDA     <= qsfp_sda(1);
    QSFP0_LPMODE  <= qsfp_lpmode(0);
    QSFP0_RESET_N <= qsfp_reset_n(0);
    QSFP0_SCL     <= qsfp_scl(0);
    QSFP0_SDA     <= qsfp_sda(0);

    qsfp_modprs_n <= QSFP1_MODPRS_N & QSFP0_MODPRS_N;
    qsfp_int_n    <= QSFP1_INT_N & QSFP0_INT_N;

    axi_spi_clk     <= misc_out(0); -- usr_x1 = 100MHz
    boot_clk        <= misc_out(2); -- usr_x2 = 200MHz
    boot_reset      <= misc_out(3);

    boot_ctrl_i : entity work.BOOT_CTRL
    generic map(
        DEVICE      => DEVICE,
        BOOT_TYPE   => 3
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

        BMC_MI_ADDR   => bmc_mi_addr_s,
        BMC_MI_DWR    => bmc_mi_dwr_s, 
        BMC_MI_WR     => bmc_mi_wr_s,
        BMC_MI_RD     => bmc_mi_rd_s,
        BMC_MI_BE     => bmc_mi_be_s,
        BMC_MI_ARDY   => bmc_mi_ardy_s,
        BMC_MI_DRD    => bmc_mi_drd_s,
        BMC_MI_DRDY   => bmc_mi_drdy_s,
        
        AXI_MI_ADDR   => axi_mi_addr_s,
        AXI_MI_DWR    => axi_mi_dwr_s, 
        AXI_MI_WR     => axi_mi_wr_s,
        AXI_MI_RD     => axi_mi_rd_s,
        AXI_MI_BE     => axi_mi_be_s,
        AXI_MI_ARDY   => axi_mi_ardy_s,
        AXI_MI_DRD    => axi_mi_drd_s,
        AXI_MI_DRDY   => axi_mi_drdy_s
    );

    bmc_ctrl_i: entity work.bmc_driver
    port map(
        CLK            => boot_clk,
        RST            => boot_reset,

        SPI_CLK        => SF2_CLK,
        SPI_NSS        => SF2_NSS,
        SPI_MOSI       => SF2_MOSI,
        SPI_MISO       => SF2_MISO,
        SPI_INT        => SF2_INT,

        -- MI32 protocol signals 
        BMC_MI_ADDR    => bmc_mi_addr_s,
        BMC_MI_DWR     => bmc_mi_dwr_s,
        BMC_MI_WR      => bmc_mi_wr_s,
        BMC_MI_RD      => bmc_mi_rd_s,
        BMC_MI_BE      => bmc_mi_be_s,
        BMC_MI_ARDY    => bmc_mi_ardy_s,
        BMC_MI_DRD     => bmc_mi_drd_s,
        BMC_MI_DRDY    => bmc_mi_drdy_s
    );

    axi_flash: entity work.axi_quad_flash_controller
    port map(
        -- clock and reset
        CLK          => boot_clk,
        SPI_CLK      => axi_spi_clk,
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

    led_driver_i: entity work.led_serial_ctrl
    generic map(
        LED_W          => 8,
        FREQ_DIV       => 10,
        LED_POLARITY   => '1',
        CNT_TIMEOUT    => (others => '1')
    )
    port map(
        CLK             => sysclk_bufg,
        RST             => sysrst,
        RED_LED         => eth_led_r,
        GREEN_LED       => eth_led_g,
        LED_SDI         => QLED_SDI,
        LED_CLK         => QLED_CLK,
        LED_LE          => QLED_LE
    );
 
    -- FPGA COMMON -------------------------------------------------------------
    usp_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 4.0,
        PLL_MULT_F              => 48.0,
        PLL_MASTER_DIV          => 10,
        PLL_OUT0_DIV_F          => 3.0,
        PLL_OUT1_DIV            => 4,
        PLL_OUT2_DIV            => 6,
        PLL_OUT3_DIV            => 12,

        USE_PCIE_CLK            => TRUE,

        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,
        PCIE_CONS               => PCIE_CONS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_LANES               => ETH_LANES,
        ETH_LANE_MAP            => ETH_LANE_MAP(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_LANE_RXPOLARITY     => ETH_LANE_RXPOLARITY(ETH_PORTS*ETH_LANES-1 downto 0),
        ETH_LANE_TXPOLARITY     => ETH_LANE_TXPOLARITY(ETH_PORTS*ETH_LANES-1 downto 0),

        QSFP_PORTS              => ETH_PORTS,
        QSFP_I2C_PORTS          => ETH_PORTS,
        ETH_PORT_LEDS           => 4,

        STATUS_LEDS             => 2,

        MISC_IN_WIDTH           => MISC_IN_WIDTH,
        MISC_OUT_WIDTH          => MISC_OUT_WIDTH,

        PCIE_ENDPOINTS          => PCIE_ENDPOINTS,
        PCIE_ENDPOINT_TYPE      => PCIE_MOD_ARCH,
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE,

        DMA_ENDPOINTS           => DMA_ENDPOINTS,
        DMA_MODULES             => DMA_MODULES,

        DMA_RX_CHANNELS         => DMA_RX_CHANNELS/DMA_MODULES,
        DMA_TX_CHANNELS         => DMA_TX_CHANNELS/DMA_MODULES,

        BOARD                   => CARD_NAME,
        DEVICE                  => DEVICE,

        AMM_FREQ_KHZ            => DDR_FREQ,
        MEM_PORTS               => DDR_PORTS,
        MEM_ADDR_WIDTH          => AMM_ADDR_WIDTH,
        MEM_DATA_WIDTH          => AMM_DATA_WIDTH,
        MEM_BURST_WIDTH         => AMM_BURST_COUNT_WIDTH
    )
    port map(
        SYSCLK                  => sysclk_bufg,
        SYSRST                  => sysrst,

        PCIE_SYSCLK_P(0)        => PCIE_SYSCLK_P,
        PCIE_SYSCLK_N(0)        => PCIE_SYSCLK_N,
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

        ETH_LED_R               => eth_led_r(ETH_PORTS*4-1 downto 0),
        ETH_LED_G               => eth_led_g(ETH_PORTS*4-1 downto 0),

        QSFP_I2C_SCL            => qsfp_scl(ETH_PORTS-1 downto 0),
        QSFP_I2C_SDA            => qsfp_sda(ETH_PORTS-1 downto 0),

        QSFP_MODSEL_N           => open,
        QSFP_LPMODE             => qsfp_lpmode(ETH_PORTS-1 downto 0),
        QSFP_RESET_N            => qsfp_reset_n(ETH_PORTS-1 downto 0),
        QSFP_MODPRS_N           => qsfp_modprs_n(ETH_PORTS-1 downto 0),
        QSFP_INT_N              => qsfp_int_n(ETH_PORTS-1 downto 0),

        STATUS_LED_G            => LED_STATUS,
        STATUS_LED_R            => open,

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

        -- Intel interface of DDR memory
        MEM_CLK                 => ddr_ui_clk,
        MEM_RST                 => ddr_ui_clk_sync_rst,

        -- Avalon interface to mem_tester
        MEM_AVMM_READY          => mem_avmm_ready,
        MEM_AVMM_READ           => mem_avmm_read,
        MEM_AVMM_WRITE          => mem_avmm_write,
        MEM_AVMM_ADDRESS        => mem_avmm_address,
        MEM_AVMM_BURSTCOUNT     => mem_avmm_burstcount,
        MEM_AVMM_WRITEDATA      => mem_avmm_writedata,
        MEM_AVMM_READDATA       => mem_avmm_readdata,
        MEM_AVMM_READDATAVALID  => mem_avmm_readdatavalid,

        EMIF_RST_REQ            => ddr_areset,
        EMIF_RST_DONE           => ddr_init_calib_complete,
        EMIF_CAL_SUCCESS        => ddr_init_calib_complete,
        EMIF_ECC_USR_INT        => (others => '0'),
        EMIF_CAL_FAIL           => (others => '0'),
        MEM_REFR_ACK            => (others => '1'),

        MISC_IN                 => misc_in,
        MISC_OUT                => misc_out
    );

end architecture;
