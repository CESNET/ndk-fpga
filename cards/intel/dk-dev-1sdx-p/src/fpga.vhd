-- fpga.vhd: DK-DEV-1SDX-P board top level entity and architecture
-- Copyright (C) 2020 CESNET z. s. p. o.
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
    -- FPGA system clock
    FPGA_SYSCLK0_100M_P     : in    std_logic;

    -- User LEDs
    USER_LED_G              : out   std_logic_vector(3 downto 0);

    -- PCIe0
    PCIE0_SYSCLK0_P         : in    std_logic;
    PCIE0_SYSCLK1_P         : in    std_logic;
    PCIE0_SYSRST_N          : in    std_logic;
    PCIE0_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE0_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE0_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE0_TX_N              : out   std_logic_vector(15 downto 0);
    PCIE0_WAKE              : out   std_logic;

    -- PCIe1
    PCIE1_SYSCLK0_P         : in    std_logic;
    PCIE1_SYSCLK1_P         : in    std_logic;
    PCIE1_SYSRST_N          : in    std_logic;
    PCIE1_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE1_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE1_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE1_TX_N              : out   std_logic_vector(15 downto 0);
    --PCIE1_WAKE              : out   std_logic

    -- QSFP
    -- =========================================================================
    ZQSFP_1V8_PORT_EN       : out   std_logic;
    ZQSFP_1V8_PORT_INT_N    : in    std_logic;
    
    CLK_312P5M_QSFP0_P      : in    std_logic;
    CLK_156P25M_QSFP0_P     : in    std_logic;
    CLK_312P5M_QSFP1_P      : in    std_logic;
    CLK_156P25M_QSFP1_P     : in    std_logic;
    CLK_312P5M_QSFP2_P      : in    std_logic;
    
    QSFP1_RX_P              : in    std_logic_vector(4-1 downto 0);
    QSFP1_RX_N              : in    std_logic_vector(4-1 downto 0);
    QSFP1_TX_P              : out   std_logic_vector(4-1 downto 0);
    QSFP1_TX_N              : out   std_logic_vector(4-1 downto 0);

    QSFP2_RX_P              : in    std_logic_vector(4-1 downto 0);
    QSFP2_RX_N              : in    std_logic_vector(4-1 downto 0);
    QSFP2_TX_P              : out   std_logic_vector(4-1 downto 0);
    QSFP2_TX_N              : out   std_logic_vector(4-1 downto 0);

    -- DDR4 TODO @xnevrk03
    -- =========================================================================
    -- I2C interface with temperature sensor
    --I2C_DDR4_DIMM_SDA       : inout std_logic;
    --I2C_DDR4_DIMM_SCL       : inout std_logic;   

    -- EMIF DIMM0 interface
    CLK_133M_DIMM_1_P       : in    std_logic;  -- DIMM1 CLK = CH0 CLK
    CLK_133M_DIMM_1_N       : in    std_logic;
    DDR4_DIMM_CH0_CK_P      : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_CK_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_A         : out   std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH0_ACT_N     : out   std_logic;
    DDR4_DIMM_CH0_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_BG        : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_CKE       : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_CS_N      : out   std_logic_vector(4-1 downto 0);
    DDR4_DIMM_CH0_ODT       : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH0_RESET_N   : out   std_logic;
    DDR4_DIMM_CH0_PAR       : out   std_logic;
    DDR4_DIMM_CH0_ALERT_N   : in    std_logic;
    DDR4_DIMM_CH0_DQS_P     : inout std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH0_DQS_N     : inout std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH0_DQ        : inout std_logic_vector(72-1 downto 0);
    --DDR4_DIMM_CH0_RZQ       : inout std_logic;
    DDR4_DIMM_CH0_RZQ       : in    std_logic;
    
    --DDR4_DIMM_CH0_C2        : out   std_logic;  --Module rank address (select of the whole memory?)
    --DDR4_DIMM_CH0_EVENT_N   : in    std_logic;  --Asserted on critical temperature
    --DDR4_DIMM_CH0_SAVE_N    : in    std_logic; 

    -- EMIF DIMM1 interface
    CLK_133M_DIMM_0_P       : in    std_logic;
    CLK_133M_DIMM_0_N       : in    std_logic;
    DDR4_DIMM_CH1_CK_P      : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_CK_N      : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_A         : out   std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH1_ACT_N     : out   std_logic_vector(0 downto 0);
    DDR4_DIMM_CH1_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_BG        : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_CKE       : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_CS_N      : out   std_logic_vector(4-1 downto 0);
    DDR4_DIMM_CH1_ODT       : out   std_logic_vector(2-1 downto 0);
    DDR4_DIMM_CH1_RESET_N   : out   std_logic_vector(0 downto 0); 
    DDR4_DIMM_CH1_PAR       : out   std_logic_vector(0 downto 0); 
    DDR4_DIMM_CH1_ALERT_N   : in    std_logic_vector(0 downto 0); 
    DDR4_DIMM_CH1_DQS_P     : inout std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH1_DQS_N     : inout std_logic_vector(18-1 downto 0);
    DDR4_DIMM_CH1_DQ        : inout std_logic_vector(72-1 downto 0);
    --DDR4_DIMM_CH1_RZQ       : inout std_logic;
    DDR4_DIMM_CH1_RZQ       : in    std_logic;
--
    --DDR4_DIMM_CH1_C2        : out   std_logic;
    --DDR4_DIMM_CH1_EVENT_N   : in    std_logic;                    
    --DDR4_DIMM_CH1_SAVE_N    : in    std_logic;          
  
    -- I2C
    -- =========================================================================
    I2C1_1V8_SCL            : inout std_logic;
    I2C1_1V8_SDA            : inout std_logic;
    I2C2_1V8_SCL            : inout std_logic;
    I2C2_1V8_SDA            : inout std_logic;
    I2C3_1V8_SCL            : inout std_logic;
    I2C3_1V8_SDA            : inout std_logic;

    BMC_I2C1_DISABLE        : out   std_logic;
    BMC_I2C2_DISABLE        : out   std_logic;
    BMC_I2C3_DISABLE        : out   std_logic
);
end entity;

architecture FULL of FPGA is

    component emif_s10dx is
    port (
        local_reset_req           : in    std_logic                      := 'X';             
        local_reset_done          : out   std_logic;                                         
        pll_ref_clk               : in    std_logic                      := 'X';             
        pll_ref_clk_out           : out   std_logic;                                         
        pll_locked                : out   std_logic;                                         
        oct_rzqin                 : in    std_logic                      := 'X';             
        mem_ck                    : out   std_logic_vector(0 downto 0);                      
        mem_ck_n                  : out   std_logic_vector(0 downto 0);                      
        mem_a                     : out   std_logic_vector(16 downto 0);                     
        mem_act_n                 : out   std_logic_vector(0 downto 0);                      
        mem_ba                    : out   std_logic_vector(1 downto 0);                      
        mem_bg                    : out   std_logic_vector(1 downto 0);                      
        mem_cke                   : out   std_logic_vector(0 downto 0);                      
        mem_cs_n                  : out   std_logic_vector(0 downto 0);                      
        mem_odt                   : out   std_logic_vector(0 downto 0);                      
        mem_reset_n               : out   std_logic_vector(0 downto 0);                      
        mem_par                   : out   std_logic_vector(0 downto 0);                      
        mem_alert_n               : in    std_logic_vector(0 downto 0)   := (others => 'X'); 
        mem_dqs                   : inout std_logic_vector(8 downto 0)   := (others => 'X'); 
        mem_dqs_n                 : inout std_logic_vector(8 downto 0)   := (others => 'X'); 
        mem_dq                    : inout std_logic_vector(71 downto 0)  := (others => 'X'); 
        mem_dbi_n                 : inout std_logic_vector(8 downto 0)   := (others => 'X'); 
        local_cal_success         : out   std_logic;                                         
        local_cal_fail            : out   std_logic;                                         
        emif_usr_reset_n          : out   std_logic;                                         
        emif_usr_clk              : out   std_logic;                                         
        ctrl_ecc_user_interrupt_0 : out   std_logic;                                         
        amm_ready_0               : out   std_logic;                                         
        amm_read_0                : in    std_logic                      := 'X';             
        amm_write_0               : in    std_logic                      := 'X';             
        amm_address_0             : in    std_logic_vector(26 downto 0)  := (others => 'X'); 
        amm_readdata_0            : out   std_logic_vector(511 downto 0);                    
        amm_writedata_0           : in    std_logic_vector(511 downto 0) := (others => 'X'); 
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)   := (others => 'X'); 
        amm_byteenable_0          : in    std_logic_vector(63 downto 0)  := (others => 'X'); 
        amm_readdatavalid_0       : out   std_logic                                          
    );
    end component;
    
    constant PCIE_LANES     : integer := 16;
    constant PCIE_CLKS      : integer := 2;
    constant PCIE_CONS      : integer := 2;
    constant MISC_IN_WIDTH  : integer := 8;
    constant MISC_OUT_WIDTH : integer := 8;
    constant ETH_LANES      : integer := 4;
    constant DMA_MODULES    : integer := tsel(DMA_400G_DEMO,1,ETH_PORTS);
    constant DMA_ENDPOINTS  : integer := tsel(PCIE_ENDPOINT_MODE=1,PCIE_ENDPOINTS,2*PCIE_ENDPOINTS);

    -- External memory interfaces (clocked at MEM_CLK)
    --constant DDR_PORTS          : integer := 2;
    --constant DDR_TYPE           : integer := 4;
    --constant DDR_A_WIDTH        : integer := 17;
    --constant DDR_BA_WIDTH       : integer := 2;
    --constant DDR_BG_WIDTH       : integer := 2;
    --constant DDR_CKE_WIDTH      : integer := 1;
    --constant DDR_CSN_WIDTH      : integer := 1;
    --constant DDR_ODT_WIDTH      : integer := 1;
    --constant DDR_CK_WIDTH       : integer := 1;
    --constant DDR_DQS_WIDTH      : integer := 9;
    --constant DDR_DBI_WIDTH      : integer := 9;
    --constant DDR_DQ_WIDTH       : integer := 72;

    constant MEM_PORTS          : integer := 2;
    constant MEM_ADDR_WIDTH     : integer := 27;
    constant MEM_DATA_WIDTH     : integer := 512;
    constant MEM_BURST_WIDTH    : integer := 7;
   
    signal ddr4_reset_n         : std_logic_vector(1 downto 0);
    signal ddr4_act_n           : std_logic_vector(1 downto 0);
    signal ddr4_par             : std_logic_vector(1 downto 0);
    signal ddr4_alert_n         : std_logic_vector(1 downto 0);

    -- External memory interfaces (clocked at MEM_CLK)
    signal mem_clk                : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_rst_n              : std_logic_vector(MEM_PORTS-1 downto 0);
    
    signal mem_avmm_ready         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_read          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_write         : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_address       : slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal mem_avmm_burstcount    : slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal mem_avmm_writedata     : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdata      : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0);
     
    signal emif_rst_req           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_ecc_usr_int       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_success       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_fail          : std_logic_vector(MEM_PORTS-1 downto 0);

begin

    PCIE0_WAKE <= '1';
    --PCIE1_WAKE <= '1';

    ZQSFP_1V8_PORT_EN <= '1';

    I2C1_1V8_SCL <= 'Z';
    I2C1_1V8_SDA <= 'Z';
    I2C3_1V8_SCL <= 'Z';
    I2C3_1V8_SDA <= 'Z';

    BMC_I2C1_DISABLE <= '0';
    BMC_I2C2_DISABLE <= '1';
    BMC_I2C3_DISABLE <= '0';

    DDR4_DIMM_CH0_RESET_N    <= ddr4_reset_n (0);
    DDR4_DIMM_CH0_ACT_N      <= ddr4_act_n   (0);
    DDR4_DIMM_CH0_PAR        <= ddr4_par     (0);
    ddr4_alert_n         (0) <= DDR4_DIMM_CH0_ALERT_N;
    DDR4_DIMM_CH1_RESET_N(0) <= ddr4_reset_n (1);
    DDR4_DIMM_CH1_ACT_N  (0) <= ddr4_act_n   (1);
    DDR4_DIMM_CH1_PAR    (0) <= ddr4_par     (1);
    ddr4_alert_n         (1) <= DDR4_DIMM_CH1_ALERT_N(0);

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
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => 2,
        ETH_PORT_LEDS           => 8,

        STATUS_LEDS             => 4,

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
        DEVICE                  => "STRATIX10",

        DMA_400G_DEMO           => DMA_400G_DEMO
    )
    port map(
        SYSCLK                  => FPGA_SYSCLK0_100M_P,
        SYSRST                  => '0',

        PCIE_SYSCLK_P           => PCIE1_SYSCLK1_P & PCIE1_SYSCLK0_P & PCIE0_SYSCLK1_P & PCIE0_SYSCLK0_P,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N           => PCIE1_SYSRST_N & PCIE0_SYSRST_N,

        PCIE_RX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_RX_P,
        PCIE_RX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => PCIE1_RX_P,

        PCIE_RX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_RX_N,
        PCIE_RX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => PCIE1_RX_N,

        PCIE_TX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_TX_P,
        PCIE_TX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => PCIE1_TX_P,

        PCIE_TX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => PCIE0_TX_N,
        PCIE_TX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => PCIE1_TX_N,

        ETH_REFCLK_P            => CLK_156P25M_QSFP1_P & CLK_156P25M_QSFP1_P,
        ETH_REFCLK_N            => (others => '0'),

        ETH_RX_P(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_RX_P,
        ETH_RX_P(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_RX_P,

        ETH_RX_N(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_RX_N,
        ETH_RX_N(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_RX_N,

        ETH_TX_P(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_TX_P,
        ETH_TX_P(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_TX_P,

        ETH_TX_N(1*ETH_LANES-1 downto 0*ETH_LANES) => QSFP1_TX_N,
        ETH_TX_N(2*ETH_LANES-1 downto 1*ETH_LANES) => QSFP2_TX_N,

        ETH_LED_R               => open,
        ETH_LED_G               => open,

        QSFP_I2C_SCL(0)         => I2C2_1V8_SCL,
        QSFP_I2C_SDA(0)         => I2C2_1V8_SDA,

        QSFP_MODSEL_N           => open,
        QSFP_LPMODE             => open,
        QSFP_RESET_N            => open,
        QSFP_MODPRS_N           => (others => '0'), -- fake module is present
        QSFP_INT_N              => (others => ZQSFP_1V8_PORT_INT_N),

        MEM_CLK                 => mem_clk,
        MEM_RST                 => not mem_rst_n,

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

        STATUS_LED_G            => USER_LED_G,
        STATUS_LED_R            => open,

        MISC_IN                 => (others => '0'),
        MISC_OUT                => open
    );


    -- =========================================================================
    --  DDR CONTROLLERS - EMIFs
    -- =========================================================================

    s10_emif_ip_ch0_i : component emif_s10dx
    port map (
        local_reset_req           => emif_rst_req           (0),
        local_reset_done          => emif_rst_done          (0),
        pll_ref_clk               => CLK_133M_DIMM_1_P,
        ----pll_ref_clk_out           => ,
        ----pll_locked                => ,

        oct_rzqin                 => DDR4_DIMM_CH0_RZQ                      ,
        mem_ck                    => DDR4_DIMM_CH0_CK_P     (0 downto 0)    ,
        mem_ck_n                  => DDR4_DIMM_CH0_CK_N     (0 downto 0)    ,
        mem_a                     => DDR4_DIMM_CH0_A        (16 downto 0)   ,
        mem_act_n                 => ddr4_act_n             (0 downto 0)    ,
        mem_ba                    => DDR4_DIMM_CH0_BA                       ,
        mem_bg                    => DDR4_DIMM_CH0_BG                       ,
        mem_cke                   => DDR4_DIMM_CH0_CKE      (0 downto 0)    ,
        mem_cs_n                  => DDR4_DIMM_CH0_CS_N     (0 downto 0)    ,
        mem_odt                   => DDR4_DIMM_CH0_ODT      (0 downto 0)    ,
        mem_reset_n               => ddr4_reset_n           (0 downto 0)    ,
        mem_par                   => ddr4_par               (0 downto 0)    ,
        mem_alert_n               => ddr4_alert_n           (0 downto 0)    ,
        mem_dqs                   => DDR4_DIMM_CH0_DQS_P    (8 downto 0)    ,
        mem_dqs_n                 => DDR4_DIMM_CH0_DQS_N    (8 downto 0)    ,
        mem_dq                    => DDR4_DIMM_CH0_DQ                       ,
        mem_dbi_n                 => DDR4_DIMM_CH0_DQS_P    (17 downto 9)   ,

        local_cal_success         => emif_cal_success       (0),
        local_cal_fail            => emif_cal_fail          (0),
        emif_usr_reset_n          => mem_rst_n              (0),
        -- Clk for user logic (generated IP uses 1/4 of mem freq = 266.666 MHz)
        emif_usr_clk              => mem_clk                (0),
        ctrl_ecc_user_interrupt_0 => emif_ecc_usr_int       (0),
        amm_ready_0               => mem_avmm_ready         (0),
        amm_read_0                => mem_avmm_read          (0),
        amm_write_0               => mem_avmm_write         (0),
        amm_address_0             => mem_avmm_address       (0),
        amm_readdata_0            => mem_avmm_readdata      (0),
        amm_writedata_0           => mem_avmm_writedata     (0),
        amm_burstcount_0          => mem_avmm_burstcount    (0),
        amm_byteenable_0          => (others=> '1'),       -- TODO
        amm_readdatavalid_0       => mem_avmm_readdatavalid (0)
    );

    s10_emif_ip_ch1_i : component emif_s10dx
    port map (
        local_reset_req           => emif_rst_req           (1),
        local_reset_done          => emif_rst_done          (1),
        pll_ref_clk               => CLK_133M_DIMM_0_P,
        ----pll_ref_clk_out           => ,
        ----pll_locked                => ,

        oct_rzqin                 => DDR4_DIMM_CH1_RZQ                      ,
        mem_ck                    => DDR4_DIMM_CH1_CK_P     (0 downto 0)    ,
        mem_ck_n                  => DDR4_DIMM_CH1_CK_N     (0 downto 0)    ,
        mem_a                     => DDR4_DIMM_CH1_A        (16 downto 0)   ,
        mem_act_n                 => ddr4_act_n             (1 downto 1)    ,
        mem_ba                    => DDR4_DIMM_CH1_BA                       ,
        mem_bg                    => DDR4_DIMM_CH1_BG                       ,
        mem_cke                   => DDR4_DIMM_CH1_CKE      (0 downto 0)    ,
        mem_cs_n                  => DDR4_DIMM_CH1_CS_N     (0 downto 0)    ,
        mem_odt                   => DDR4_DIMM_CH1_ODT      (0 downto 0)    ,
        mem_reset_n               => ddr4_reset_n           (1 downto 1)    ,
        mem_par                   => ddr4_par               (1 downto 1)    ,
        mem_alert_n               => ddr4_alert_n           (1 downto 1)    ,
        mem_dqs                   => DDR4_DIMM_CH1_DQS_P    (8 downto 0)    ,
        mem_dqs_n                 => DDR4_DIMM_CH1_DQS_N    (8 downto 0)    ,
        mem_dq                    => DDR4_DIMM_CH1_DQ                       ,
        mem_dbi_n                 => DDR4_DIMM_CH1_DQS_P    (17 downto 9)   ,

        local_cal_success         => emif_cal_success       (1),
        local_cal_fail            => emif_cal_fail          (1),
        emif_usr_reset_n          => mem_rst_n              (1),
        emif_usr_clk              => mem_clk                (1),
        ctrl_ecc_user_interrupt_0 => emif_ecc_usr_int       (1),
        amm_ready_0               => mem_avmm_ready         (1),
        amm_read_0                => mem_avmm_read          (1),
        amm_write_0               => mem_avmm_write         (1),
        amm_address_0             => mem_avmm_address       (1),
        amm_readdata_0            => mem_avmm_readdata      (1),
        amm_writedata_0           => mem_avmm_writedata     (1),
        amm_burstcount_0          => mem_avmm_burstcount    (1),
        amm_byteenable_0          => (others=> '1'),       -- TODO
        amm_readdatavalid_0       => mem_avmm_readdatavalid (1)
    );

end architecture;
