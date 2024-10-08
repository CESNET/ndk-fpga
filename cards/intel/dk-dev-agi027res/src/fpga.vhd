-- fpga.vhd: DK-DEV-AGI027RES board top level entity and architecture
-- Copyright (C) 2021 CESNET z. s. p. o.
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
    clk_sys_100m_p        : in    std_logic;
    --clk_sys_bak_50m_p     : in    std_logic;

    -- Board/FPGA control
    cpu_1v2_resetn        : in    std_logic;
    fpga_i2c_en           : out   std_logic;
    fpga_i2c1_scl         : inout std_logic;
    fpga_i2c1_sda         : inout std_logic;
    fpga_i2c2_en          : out   std_logic;
    fpga_i2c2_scl         : inout std_logic;
    fpga_i2c2_sda         : inout std_logic;
    
    -- User LEDs
    fpga_led              : out   std_logic_vector(3 downto 0);

    -- PCIe0
    -- =========================================================================
    refclk_pcie_14c_ch0_p : in    std_logic;
    refclk_pcie_14c_ch1_p : in    std_logic;

    pcie_ep_tx_p          : out   std_logic_vector(15 downto 0);
    pcie_ep_tx_n          : out   std_logic_vector(15 downto 0);
    pcie_ep_rx_p          : in    std_logic_vector(15 downto 0);
    pcie_ep_rx_n          : in    std_logic_vector(15 downto 0);

    fpga_pcie_perstn      : in    std_logic;
    pcie_1v2_clkreqn      : out   std_logic;
    pcie_ep_waken         : in    std_logic;

    -- PCIe1 (CXL)
    -- =========================================================================
    refclk_cxl_15c_ch0_p  : in    std_logic;
    refclk_cxl_15c_ch1_p  : in    std_logic;

    cxl_tx_p              : out   std_logic_vector(15 downto 0);
    cxl_tx_n              : out   std_logic_vector(15 downto 0);
    cxl_rx_p              : in    std_logic_vector(15 downto 0);
    cxl_rx_n              : in    std_logic_vector(15 downto 0);

    fpga_cxl_perstn       : in    std_logic;

    -- QSFP
    -- =========================================================================
    qsfpdd1_fpga_led      : out   std_logic_vector(3-1 downto 0);
    qsfpdd0_fpga_led      : out   std_logic_vector(3-1 downto 0);
    
    qsfpdd_1v2_port_en    : out   std_logic;
    qsfpdd_1v2_port_int_n : in    std_logic;
    
    -- QSFPDD reference clock 100MHz from U22
    --refclk_fgt12ach0_p    : in    std_logic;
    -- QSFPDD reference clock 153.6MHz from U22
    --refclk_fgt12ach3_p    : in    std_logic;
    -- QSFPDD reference clock 156.25MHz from U22
    refclk_fgt12ach4_p    : in    std_logic;
    -- QSFPDD reference clock 156.25MHz from U22
    --refclk_fgt12ach5_p    : in    std_logic;
    -- QSFPDD reference clock 184.32MHz from U22
    --refclk_fgt12ach6_p    : in    std_logic;
    
    --qsfpdd0_rx_p          : in    std_logic_vector(8-1 downto 0);
    --qsfpdd0_rx_n          : in    std_logic_vector(8-1 downto 0);
    --qsfpdd0_tx_p          : out   std_logic_vector(8-1 downto 0);
    --qsfpdd0_tx_n          : out   std_logic_vector(8-1 downto 0);

    qsfpdd1_rx_p          : in    std_logic_vector(8-1 downto 0);
    qsfpdd1_rx_n          : in    std_logic_vector(8-1 downto 0);
    qsfpdd1_tx_p          : out   std_logic_vector(8-1 downto 0);
    qsfpdd1_tx_n          : out   std_logic_vector(8-1 downto 0);

    -- DDR4
    -- =========================================================================
    CLK_DDR4_CH2_P          : in    std_logic; -- 33.333 MHz ref clk
    CLK_DDR4_CH2_N          : in    std_logic;

    -- DDR4 DIMMA interface
    DDR4_DIMMA_CK_P0        : out   std_logic;
    DDR4_DIMMA_CK_N0        : out   std_logic;
    DDR4_DIMMA_CKE          : out   std_logic_vector(0 downto 0);
    DDR4_DIMMA_CS_N         : out   std_logic_vector(0 downto 0);
    DDR4_DIMMA_ODT          : out   std_logic_vector(0 downto 0);

    -- DDR4 DIMMB interface
    -- TODO

    -- DDR4 common interface
    DDR4_DDIMM_A            : out   std_logic_vector(17-1 downto 0);
    DDR4_DDIMM_ACT_N        : out   std_logic_vector(0 downto 0);
    DDR4_DDIMM_BA           : out   std_logic_vector(2-1 downto 0);
    DDR4_DDIMM_BG           : out   std_logic_vector(2-1 downto 0);
    DDR4_DDIMM_RESET_N      : out   std_logic_vector(0 downto 0);
    DDR4_DDIMM_PAR          : out   std_logic;  --_vector(0 downto 0);
    DDR4_DDIMM_ALERT_N      : in    std_logic;
    DDR4_DDIMM_DQS_P        : inout std_logic_vector(18-1 downto 0);
    DDR4_DDIMM_DQS_N        : inout std_logic_vector(18-1 downto 0);
    DDR4_DDIMM_DQ           : inout std_logic_vector(72-1 downto 0);
    --DDR4_DDIMM_DBI_N        : inout std_logic_vector(9-1 downto 0);
    --DDR4_DDIMM_TDQS_N       : inout std_logic_vector(18-1 downto 9);
    DDR4_DDIMM_RZQ          : in    std_logic;

    -- DDR4 others
    -- TODO FPGA_DIMM_SCL, SDA
    FPGA_DIMM_SCL           : inout std_logic;
    FPGA_DIMM_SDA           : inout std_logic
);
end entity;

architecture FULL of FPGA is

    component emif_agi027 is
    port (
        local_reset_req           : in    std_logic                       := 'X';             
        local_reset_done          : out   std_logic;                                          
        pll_ref_clk               : in    std_logic                       := 'X';             
        pll_locked                : out   std_logic;                                          
        oct_rzqin                 : in    std_logic                       := 'X';             
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
        mem_alert_n               : in    std_logic_vector(0 downto 0)    := (others => 'X'); 
        mem_dqs                   : inout std_logic_vector(17 downto 0)   := (others => 'X'); 
        mem_dqs_n                 : inout std_logic_vector(17 downto 0)   := (others => 'X'); 
        mem_dq                    : inout std_logic_vector(71 downto 0)   := (others => 'X'); 
        local_cal_success         : out   std_logic;                                          
        local_cal_fail            : out   std_logic;                                          
        calbus_read               : in    std_logic                       := 'X';             
        calbus_write              : in    std_logic                       := 'X';             
        calbus_address            : in    std_logic_vector(19 downto 0)   := (others => 'X'); 
        calbus_wdata              : in    std_logic_vector(31 downto 0)   := (others => 'X'); 
        calbus_rdata              : out   std_logic_vector(31 downto 0);                      
        calbus_seq_param_tbl      : out   std_logic_vector(4095 downto 0);                    
        calbus_clk                : in    std_logic                       := 'X';             
        emif_usr_reset_n          : out   std_logic;                                          
        emif_usr_clk              : out   std_logic;                                          
        ctrl_ecc_user_interrupt_0 : out   std_logic;                                          
        amm_ready_0               : out   std_logic;                                          
        amm_read_0                : in    std_logic                       := 'X';             
        amm_write_0               : in    std_logic                       := 'X';             
        amm_address_0             : in    std_logic_vector(27 downto 0)   := (others => 'X'); 
        amm_readdata_0            : out   std_logic_vector(511 downto 0);                     
        amm_writedata_0           : in    std_logic_vector(511 downto 0)  := (others => 'X'); 
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)    := (others => 'X'); 
        amm_readdatavalid_0       : out   std_logic;
        mmr_slave_waitrequest_0        : out   std_logic;                                          -- waitrequest
        mmr_slave_read_0               : in    std_logic                       := 'X';             -- read
        mmr_slave_write_0              : in    std_logic                       := 'X';             -- write
        mmr_slave_address_0            : in    std_logic_vector(9 downto 0)    := (others => 'X'); -- address
        mmr_slave_readdata_0           : out   std_logic_vector(31 downto 0);                      -- readdata
        mmr_slave_writedata_0          : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- writedata
        mmr_slave_burstcount_0         : in    std_logic_vector(1 downto 0)    := (others => 'X'); -- burstcount
        mmr_slave_beginbursttransfer_0 : in    std_logic                       := 'X';             -- beginbursttransfer
        mmr_slave_readdatavalid_0      : out   std_logic;                                          -- readdatavalid
        ctrl_auto_precharge_req_0 : in    std_logic                       := 'X'
    );
    end component;

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

    constant DEVICE                 : string := "AGILEX";

    constant PCIE_LANES             : integer := 16;
    constant PCIE_CLKS              : integer := 2;
    constant PCIE_CONS              : integer := 2;
    constant MISC_IN_WIDTH          : integer := 8;
    constant MISC_OUT_WIDTH         : integer := 8;
    constant ETH_LANES              : integer := 8;
    constant DMA_MODULES            : integer := ETH_PORTS;
    constant DMA_ENDPOINTS          : integer := f_dma_endpoints(PCIE_ENDPOINTS,PCIE_ENDPOINT_MODE,PCIE_GEN);

    constant MEM_PORTS              : integer := 1;
    constant MEM_ADDR_WIDTH         : integer := 28;
    constant MEM_DATA_WIDTH         : integer := 512;
    constant MEM_BURST_WIDTH        : integer := 7;

    constant MEM_RANK_CNT           : integer := 4; -- For emif_refresh
    constant MEM_REFR_PERIOD_WIDTH  : integer := 32;
    constant MEM_DEF_REFR_PERIOD    : integer := 10000; -- for each MEM port
    constant MEM_MMR_ADDR_WIDTH     : integer := 10;
    constant MEM_MMR_DATA_WIDTH     : integer := 32;
    constant MEM_MMR_BURST_WIDTH    : integer := 2;
 
    signal calbus_read              : std_logic;                                          
    signal calbus_write             : std_logic;                                          
    signal calbus_address           : std_logic_vector(19 downto 0);                      
    signal calbus_wdata             : std_logic_vector(31 downto 0);                      
    signal calbus_rdata             : std_logic_vector(31 downto 0)   := (others => 'X'); 
    signal calbus_seq_param_tbl     : std_logic_vector(4095 downto 0) := (others => 'X'); 
    signal calbus_clk               : std_logic;

    -- External memory interfaces (clocked at MEM_CLK)
    signal mem_clk                          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_rst                          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_rst_n                        : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_pll_locked                   : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_pll_locked_sync              : std_logic_vector(MEM_PORTS-1 downto 0);
    
    signal mem_avmm_ready                   : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_read                    : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_write                   : std_logic_vector(MEM_PORTS-1 downto 0);
    signal mem_avmm_address                 : slv_array_t(MEM_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal mem_avmm_burstcount              : slv_array_t(MEM_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal mem_avmm_writedata               : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdata                : slv_array_t(MEM_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdatavalid           : std_logic_vector(MEM_PORTS-1 downto 0);

    signal mem_mmr_address                  : slv_array_t(MEM_PORTS - 1 downto 0)(MEM_MMR_ADDR_WIDTH-1 downto 0);
    signal mem_mmr_read_data                : slv_array_t(MEM_PORTS - 1 downto 0)(MEM_MMR_DATA_WIDTH-1 downto 0);
    signal mem_mmr_write_data               : slv_array_t(MEM_PORTS - 1 downto 0)(MEM_MMR_DATA_WIDTH-1 downto 0);
    signal mem_mmr_burst_count              : slv_array_t(MEM_PORTS - 1 downto 0)(MEM_MMR_BURST_WIDTH-1 downto 0);
    signal mem_mmr_waitrequest              : std_logic_vector(MEM_PORTS - 1 downto 0);                   
    signal mem_mmr_read                     : std_logic_vector(MEM_PORTS - 1 downto 0);
    signal mem_mmr_write                    : std_logic_vector(MEM_PORTS - 1 downto 0);
    signal mem_mmr_begin_burst_transfer     : std_logic_vector(MEM_PORTS - 1 downto 0);
    signal mem_mmr_read_data_valid          : std_logic_vector(MEM_PORTS - 1 downto 0);                   

    signal mem_refr_req                     : std_logic_vector(MEM_PORTS - 1 downto 0);
    signal mem_refr_ack                     : std_logic_vector(MEM_PORTS - 1 downto 0);
    signal mem_refr_period                  : slv_array_t(MEM_PORTS - 1 downto 0)(MEM_REFR_PERIOD_WIDTH - 1 downto 0);
     
    signal emif_rst_req                     : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done                    : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_ecc_usr_int                 : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_success                 : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_fail                    : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_auto_precharge              : std_logic_vector(MEM_PORTS-1 downto 0);

    signal ddr4_dimma_ck_p_intern           : std_logic_vector(0 downto 0);
    signal ddr4_dimma_ck_n_intern           : std_logic_vector(0 downto 0);

begin

    fpga_i2c_en   <= 'Z';
    fpga_i2c1_scl <= 'Z';
    fpga_i2c1_sda <= 'Z';
    fpga_i2c2_en  <= 'Z';
    --fpga_i2c2_scl <= 'Z';
    --fpga_i2c2_sda <= 'Z';
    FPGA_DIMM_SCL <= 'Z';
    FPGA_DIMM_SDA <= 'Z';

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

        mem_rst(i) <= not (mem_rst_n(i) and mem_pll_locked_sync(i));
    end generate;

    qsfpdd_1v2_port_en <= '1';

    pcie_1v2_clkreqn <= '0';

    ag_i : entity work.FPGA_COMMON
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

        PCI_VENDOR_ID           => X"18EC",
        PCI_DEVICE_ID           => X"C400",
        PCI_SUBVENDOR_ID        => X"0000",
        PCI_SUBDEVICE_ID        => X"0000",

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_LANES               => ETH_LANES,

        QSFP_PORTS              => ETH_PORTS,
        ETH_PORT_LEDS           => 1,

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
        MEM_REFR_PERIOD_WIDTH   => MEM_REFR_PERIOD_WIDTH,
        MEM_DEF_REFR_PERIOD     => MEM_DEF_REFR_PERIOD,
        AMM_FREQ_KHZ            => 333_332,

        BOARD                   => CARD_NAME,
        DEVICE                  => DEVICE
    )
    port map(
        SYSCLK                  => clk_sys_100m_p,
        SYSRST                  => '0',

        PCIE_SYSCLK_P           => refclk_cxl_15c_ch1_p & refclk_cxl_15c_ch0_p & refclk_pcie_14c_ch1_p & refclk_pcie_14c_ch0_p,
        PCIE_SYSCLK_N           => (others => '0'),
        PCIE_SYSRST_N           => fpga_cxl_perstn & fpga_pcie_perstn,

        PCIE_RX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => pcie_ep_rx_p,
        PCIE_RX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => cxl_rx_p,

        PCIE_RX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => pcie_ep_rx_n,
        PCIE_RX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => cxl_rx_n,

        PCIE_TX_P(1*PCIE_LANES-1 downto 0*PCIE_LANES) => pcie_ep_tx_p,
        PCIE_TX_P(2*PCIE_LANES-1 downto 1*PCIE_LANES) => cxl_tx_p,

        PCIE_TX_N(1*PCIE_LANES-1 downto 0*PCIE_LANES) => pcie_ep_tx_n,
        PCIE_TX_N(2*PCIE_LANES-1 downto 1*PCIE_LANES) => cxl_tx_n,

        ETH_REFCLK_P(0)         => refclk_fgt12ach4_p,
        ETH_REFCLK_N(0)         => '0',

        ETH_RX_P => qsfpdd1_rx_p,
        ETH_RX_N => qsfpdd1_rx_n,
        ETH_TX_P => qsfpdd1_tx_p,
        ETH_TX_N => qsfpdd1_tx_n,

        ETH_LED_R(0)            => qsfpdd1_fpga_led(2),
        ETH_LED_G(0)            => qsfpdd1_fpga_led(0),

        QSFP_I2C_SCL(0)         => fpga_i2c2_scl,
        QSFP_I2C_SDA(0)         => fpga_i2c2_sda,

        QSFP_MODSEL_N           => open,
        QSFP_LPMODE             => open,
        QSFP_RESET_N            => open,
        QSFP_MODPRS_N           => (others => '0'), -- fake module is present
        QSFP_INT_N              => (others => qsfpdd_1v2_port_int_n),

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

        MEM_REFR_PERIOD         => mem_refr_period,
        MEM_REFR_REQ            => mem_refr_req,
        MEM_REFR_ACK            => mem_refr_ack,

        EMIF_RST_REQ            => emif_rst_req,
        EMIF_RST_DONE           => emif_rst_done,
        EMIF_ECC_USR_INT        => emif_ecc_usr_int,
        EMIF_CAL_SUCCESS        => emif_cal_success,
        EMIF_CAL_FAIL           => emif_cal_fail,
        EMIF_AUTO_PRECHARGE     => emif_auto_precharge,

        STATUS_LED_G            => fpga_led,
        STATUS_LED_R            => open,

        MISC_IN                 => (others => '0'),
        MISC_OUT                => open
    );

    -- =========================================================================
    --  DDR CONTROLLERS - EMIFs
    -- =========================================================================

    emif_0 : component emif_agi027
    port map (
        local_reset_req                 => emif_rst_req(0),
        local_reset_done                => emif_rst_done(0),
        pll_ref_clk                     => CLK_DDR4_CH2_P,
        pll_locked                      => mem_pll_locked(0),
        oct_rzqin                       => DDR4_DDIMM_RZQ,
        mem_ck   (0)                    => DDR4_DIMMA_CK_P0,
        mem_ck_n (0)                    => DDR4_DIMMA_CK_N0,
        mem_a                           => DDR4_DDIMM_A,
        mem_act_n                       => DDR4_DDIMM_ACT_N,
        mem_ba                          => DDR4_DDIMM_BA,
        mem_bg                          => DDR4_DDIMM_BG,
        mem_cke                         => DDR4_DIMMA_CKE,
        mem_cs_n                        => DDR4_DIMMA_CS_N,
        mem_odt                         => DDR4_DIMMA_ODT,
        mem_reset_n                     => DDR4_DDIMM_RESET_N,
        mem_par(0)                      => DDR4_DDIMM_PAR,
        mem_alert_n(0)                  => DDR4_DDIMM_ALERT_N,
        mem_dqs                         => DDR4_DDIMM_DQS_P,
        mem_dqs_n                       => DDR4_DDIMM_DQS_N,
        mem_dq                          => DDR4_DDIMM_DQ,
        local_cal_success               => emif_cal_success(0),
        local_cal_fail                  => emif_cal_fail(0),
        calbus_read                     => calbus_read,   
        calbus_write                    => calbus_write,  
        calbus_address                  => calbus_address,
        calbus_wdata                    => calbus_wdata,  
        calbus_rdata                    => calbus_rdata,  
        calbus_seq_param_tbl            => calbus_seq_param_tbl, 
        calbus_clk                      => calbus_clk,                
        emif_usr_reset_n                => mem_rst_n(0), 
        emif_usr_clk                    => mem_clk(0), 
        ctrl_ecc_user_interrupt_0       => emif_ecc_usr_int(0), 
        amm_ready_0                     => mem_avmm_ready(0),
        amm_read_0                      => mem_avmm_read(0),
        amm_write_0                     => mem_avmm_write(0),
        amm_address_0                   => mem_avmm_address(0),
        amm_readdata_0                  => mem_avmm_readdata(0),
        amm_writedata_0                 => mem_avmm_writedata(0),
        amm_burstcount_0                => mem_avmm_burstcount(0),
        amm_readdatavalid_0             => mem_avmm_readdatavalid(0),
        mmr_slave_waitrequest_0         => mem_mmr_waitrequest(0),
        mmr_slave_read_0                => mem_mmr_read(0), 
        mmr_slave_write_0               => mem_mmr_write(0),      
        mmr_slave_address_0             => mem_mmr_address(0),    
        mmr_slave_readdata_0            => mem_mmr_read_data(0),   
        mmr_slave_writedata_0           => mem_mmr_write_data(0),  
        mmr_slave_burstcount_0          => mem_mmr_burst_count(0), 
        mmr_slave_beginbursttransfer_0  => mem_mmr_begin_burst_transfer(0),
        mmr_slave_readdatavalid_0       => mem_mmr_read_data_valid(0),     
        ctrl_auto_precharge_req_0       => emif_auto_precharge(0)
    );
     
    -- Each EMIF instance must be connected to the I/O SSM.
    -- Only one calibration IP is allowed for each I/O row. All the EMIFs in the same I/O row
    -- must be connected to the same calibration I/P. You can specify the number of EMIF
    -- interfaces to be connected to the calibration IP when parameterizing the IP. 
    
    emif_cal_0 : component emif_agi027_cal
    port map (
        calbus_read_0               => calbus_read,              
        calbus_write_0              => calbus_write,       
        calbus_address_0            => calbus_address,     
        calbus_wdata_0              => calbus_wdata,    
        calbus_rdata_0              => calbus_rdata,       
        calbus_seq_param_tbl_0      => calbus_seq_param_tbl,
        calbus_clk                  => calbus_clk,
        cal_debug_clk_clk           => mem_clk(0),
        cal_debug_reset_n_reset     => mem_rst_n(0)
    );

    emif_refresh_i : entity work.EMIF_REFRESH
    generic map (
        AMM_DATA_WIDTH          => MEM_MMR_DATA_WIDTH,
        AMM_ADDR_WIDTH          => MEM_MMR_ADDR_WIDTH,
        AMM_BURST_COUNT_WIDTH   => MEM_MMR_BURST_WIDTH,

        PERIODIC_REFRESH        => true,
        REFRESH_PERIOD_WIDTH    => MEM_REFR_PERIOD_WIDTH,

        RANK_CNT                => MEM_RANK_CNT,
        DEVICE                  => DEVICE
    )
    port map (
        CLK                     => mem_clk (0),
        RST                     => mem_rst (0),

        REFRESH                 => (others => mem_refr_req  (0)),
        REFRESH_PERIOD_TICKS    => mem_refr_period          (0),
        REFRESH_DONE_ANY        => mem_refr_ack             (0),

        AMM_READY               => not mem_mmr_waitrequest  (0), 
        AMM_READ                => mem_mmr_read             (0), 
        AMM_WRITE               => mem_mmr_write            (0), 
        AMM_ADDRESS             => mem_mmr_address          (0), 
        AMM_READ_DATA           => mem_mmr_read_data        (0), 
        AMM_WRITE_DATA          => mem_mmr_write_data       (0), 
        AMM_BURST_COUNT         => mem_mmr_burst_count      (0), 
        AMM_READ_DATA_VALID     => mem_mmr_read_data_valid  (0)
    );

end architecture;
