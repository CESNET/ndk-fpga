-- fpga.vhd: Terasic A2700 card top-level entity and architecture
-- Copyright (C) 2024 DynaNIC Semiconductors, Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.ndk_fpga_top_pkg.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;

-- Note: Boot is currently handled by the SDM
entity FPGA is
port (

    -- =========================================================================
    --  GENERAL CLOCKS AND PLL STATUS SIGNALS
    -- =========================================================================
    -- External differential clocks (programmable via Ext. PLL)
    AG_SYSCLK0_P     : in    std_logic; -- N/A MHz
    -- SI5397A Oscillator - 50 MHz
    AG_SYSCLK1_P     : in    std_logic;

    -- Warning! There are 100 MHz clocks available which cannot be used at the
    -- moment because of a bug in Quartus 24.1 and 24.2 which makes it impossible
    -- to implement the EMIF IP core if there is a clock instantiated in the same
    -- I/O bank. (PIN_LB60)

    -- If you decide to use 100 MHz clock, be sure to regenerate the iopll IP core
    -- for the new frequency

    -- It is possible to use 100 MHz clock if there is no EMIF IP core or Quartus
    -- will instantiate itself (without .qsf constraint).

    -- =========================================================================
    --  PCIE INTERFACE
    -- =========================================================================
    PCIE_CLK0_P            : in    std_logic;
    PCIE_CLK1_P            : in    std_logic;
    PCIE_PERST_N           : in    std_logic;
    PCIE_RX_P              : in    std_logic_vector(15 downto 0);
    PCIE_RX_N              : in    std_logic_vector(15 downto 0);
    PCIE_TX_P              : out   std_logic_vector(15 downto 0);
    PCIE_TX_N              : out   std_logic_vector(15 downto 0);
    -- =========================================================================
    --  QSFP-DD INTERFACES - F-TILE
    -- =========================================================================
    QSFP_I2C_SCL            : inout std_logic;
    QSFP_I2C_SDA            : inout std_logic;
    QSFP_MODSEL_N           : out   std_logic;
    QSFP_INITMODE           : out   std_logic;
    QSFP_RST_N              : out   std_logic;
    QSFP_MODPRS_N           : in    std_logic;
    QSFP_INT_N              : in    std_logic;
    QSFP_REFCLK0_P          : in    std_logic;
    QSFP_RX_P               : in    std_logic_vector(7 downto 0);
    QSFP_RX_N               : in    std_logic_vector(7 downto 0);
    QSFP_TX_P               : out   std_logic_vector(7 downto 0);
    QSFP_TX_N               : out   std_logic_vector(7 downto 0);
    -- =========================================================================
    --  SI5397A - External Clock Generator (QSFP & SYSCLK)
    -- =========================================================================
    SI5397A_I2C_SCL         : inout std_logic;
    SI5397A_I2C_SDA         : inout std_logic;
    SI5397A_OE_n            : out   std_logic;
    SI5397A_RST_n           : out   std_logic;
    -- =========================================================================
    --  HPS (HARD PROCESSOR SYSTEM) INTERFACE - Available but not supported
    -- =========================================================================
    -- =========================================================================
    --  SODIMM INTERFACES
    -- =========================================================================
    -- SODIMM_REFCLK_P : DDR4 B port Reference Clock_p - 33.333 MHz (Si540)
    -- SODIMM_OCT_RZQ  : Calibrated pins for OCT block
    -- SODIMM_PCK      : Clock p
    -- SODIMM_NCK      : Clock n
    -- SODIMM_A        : Address
    -- SODIMM_NACT     : Activation Command Input n
    -- SODIMM_BA       : Bank Select
    -- SODIMM_BG       : Bank Group Select
    -- SODIMM_CKE      : Clock Enable pin
    -- SODIMM_NCS      : Chip Select n
    -- SODIMM_ODT      : On Die Termination
    -- SODIMM_NRST     : Chip Reset n
    -- SODIMM_PAR      : Command and Address Parity Input
    -- SODIMM_NALERT   : Register Alert n
    -- SODIMM_PDQS     : Data Strobe p
    -- SODIMM_NDQS     : Data strobe n
    -- SODIMM_DM_DBI   : Data Bus inversion n
    -- SODIMM_DQ       : Data

    -- Note that there are more pins available, but calibration will fail if
    -- there is not enough DDR memory. These pins are available in the .qsf file

    SODIMM_HPS_REFCLK_P : in    std_logic;
    SODIMM_HPS_OCT_RZQ  : in    std_logic;
    SODIMM_HPS_PCK      : out   std_logic;
    SODIMM_HPS_NCK      : out   std_logic;
    SODIMM_HPS_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM_HPS_NACT     : out   std_logic;
    SODIMM_HPS_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM_HPS_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM_HPS_CKE      : out   std_logic;
    SODIMM_HPS_NCS      : out   std_logic;
    SODIMM_HPS_ODT      : out   std_logic;
    SODIMM_HPS_NRST     : out   std_logic;
    SODIMM_HPS_PAR      : out   std_logic;
    SODIMM_HPS_NALERT   : in    std_logic;
    SODIMM_HPS_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM_HPS_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM_HPS_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM_HPS_DQ       : inout std_logic_vector(72-1 downto 0);

    SODIMM0_REFCLK_P : in    std_logic;
    SODIMM0_OCT_RZQ  : in    std_logic;
    SODIMM0_PCK      : out   std_logic;
    SODIMM0_NCK      : out   std_logic;
    SODIMM0_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM0_NACT     : out   std_logic;
    SODIMM0_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM0_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM0_CKE      : out   std_logic;
    SODIMM0_NCS      : out   std_logic;
    SODIMM0_ODT      : out   std_logic;
    SODIMM0_NRST     : out   std_logic;
    SODIMM0_PAR      : out   std_logic;
    SODIMM0_NALERT   : in    std_logic;
    SODIMM0_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM0_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM0_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM0_DQ       : inout std_logic_vector(72-1 downto 0);

    SODIMM1_REFCLK_P : in    std_logic;
    SODIMM1_OCT_RZQ  : in    std_logic;
    SODIMM1_PCK      : out   std_logic;
    SODIMM1_NCK      : out   std_logic;
    SODIMM1_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM1_NACT     : out   std_logic;
    SODIMM1_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM1_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM1_CKE      : out   std_logic;
    SODIMM1_NCS      : out   std_logic;
    SODIMM1_ODT      : out   std_logic;
    SODIMM1_NRST     : out   std_logic;
    SODIMM1_PAR      : out   std_logic;
    SODIMM1_NALERT   : in    std_logic;
    SODIMM1_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM1_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM1_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM1_DQ       : inout std_logic_vector(72-1 downto 0);

    SODIMM2_REFCLK_P : in    std_logic;
    SODIMM2_OCT_RZQ  : in    std_logic;
    SODIMM2_PCK      : out   std_logic;
    SODIMM2_NCK      : out   std_logic;
    SODIMM2_A        : out   std_logic_vector(17-1 downto 0);
    SODIMM2_NACT     : out   std_logic;
    SODIMM2_BA       : out   std_logic_vector(2-1 downto 0);
    SODIMM2_BG       : out   std_logic_vector(2-1 downto 0);
    SODIMM2_CKE      : out   std_logic;
    SODIMM2_NCS      : out   std_logic;
    SODIMM2_ODT      : out   std_logic;
    SODIMM2_NRST     : out   std_logic;
    SODIMM2_PAR      : out   std_logic;
    SODIMM2_NALERT   : in    std_logic;
    SODIMM2_PDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM2_NDQS     : inout std_logic_vector(9-1 downto 0);
    SODIMM2_DM_DBI   : inout std_logic_vector(9-1 downto 0);
    SODIMM2_DQ       : inout std_logic_vector(72-1 downto 0)

);
end entity;

architecture FULL of FPGA is
    -- This IP enable usage of HPS reserved SODIMM in the FPGA logic
    component sodimm_hps is
        port (
            local_reset_req           : in    std_logic                       := 'X';             -- local_reset_req
            local_reset_done          : out   std_logic;                                          -- local_reset_done
            pll_ref_clk               : in    std_logic                       := 'X';             -- clk
            oct_rzqin                 : in    std_logic                       := 'X';             -- oct_rzqin
            mem_ck                    : out   std_logic_vector(0 downto 0);                       -- mem_ck
            mem_ck_n                  : out   std_logic_vector(0 downto 0);                       -- mem_ck_n
            mem_a                     : out   std_logic_vector(16 downto 0);                      -- mem_a
            mem_act_n                 : out   std_logic_vector(0 downto 0);                       -- mem_act_n
            mem_ba                    : out   std_logic_vector(1 downto 0);                       -- mem_ba
            mem_bg                    : out   std_logic_vector(1 downto 0);                       -- mem_bg
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
            emif_usr_reset_n          : out   std_logic;                                          -- reset_n
            emif_usr_clk              : out   std_logic;                                          -- clk
            amm_ready_0               : out   std_logic;                                          -- waitrequest_n
            amm_read_0                : in    std_logic                       := 'X';             -- read
            amm_write_0               : in    std_logic                       := 'X';             -- write
            amm_address_0             : in    std_logic_vector(26 downto 0)   := (others => 'X'); -- address
            amm_readdata_0            : out   std_logic_vector(511 downto 0);                     -- readdata
            amm_writedata_0           : in    std_logic_vector(511 downto 0)  := (others => 'X'); -- writedata
            amm_burstcount_0          : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
            amm_byteenable_0          : in    std_logic_vector(63 downto 0)   := (others => 'X'); -- byteenable
            amm_readdatavalid_0       : out   std_logic;                                          -- readdatavalid
            calbus_read               : in    std_logic                       := 'X';             -- calbus_read
            calbus_write              : in    std_logic                       := 'X';             -- calbus_write
            calbus_address            : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
            calbus_wdata              : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
            calbus_rdata              : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
            calbus_seq_param_tbl      : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
            calbus_clk                : in    std_logic                       := 'X';             -- clk

            ctrl_ecc_user_interrupt_0 : out   std_logic                                           -- ctrl_ecc_user_interrupt

        );
    end component sodimm_hps;

    -- Regular EMIF IP
    component sodimm is
        port (
            local_reset_req           : in    std_logic                       := 'X';             -- local_reset_req
            local_reset_done          : out   std_logic;                                          -- local_reset_done
            pll_ref_clk               : in    std_logic                       := 'X';             -- clk
            oct_rzqin                 : in    std_logic                       := 'X';             -- oct_rzqin
            mem_ck                    : out   std_logic_vector(0 downto 0);                       -- mem_ck
            mem_ck_n                  : out   std_logic_vector(0 downto 0);                       -- mem_ck_n
            mem_a                     : out   std_logic_vector(16 downto 0);                      -- mem_a
            mem_act_n                 : out   std_logic_vector(0 downto 0);                       -- mem_act_n
            mem_ba                    : out   std_logic_vector(1 downto 0);                       -- mem_ba
            mem_bg                    : out   std_logic_vector(1 downto 0);                       -- mem_bg
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
    end component sodimm;

    -- Each calibration IP can handle two emif controllers (due to the EMIF hard IP placement)
    component sodimm_cal is
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
            calbus_seq_param_tbl_1 : in  std_logic_vector(4095 downto 0) := (others => 'X'); -- calbus_seq_param_tbl;
            calbus_clk             : out std_logic                                           -- clk
        );
    end component sodimm_cal;

    constant PCIE_CLKS       : integer := 2;
    constant PCIE_CONS       : integer := 1;
    constant MISC_IN_WIDTH   : integer := 64;
    constant MISC_OUT_WIDTH  : integer := 64 + 5;
    constant ETH_LANES       : integer := 8;
    constant MEM_PORTS       : integer := DDR4_PORTS;
    constant MEM_ADDR_WIDTH  : integer := 27;
    constant MEM_DATA_WIDTH  : integer := 512;
    constant MEM_BURST_WIDTH : integer := 7;
    constant AMM_FREQ_KHZ    : integer := 333333;
    constant DEVICE          : string  := "AGILEX";

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
    signal mem_rst_n_reg          : std_logic_vector(MEM_PORTS-1 downto 0);

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

    signal misc_in                : std_logic_vector(MISC_IN_WIDTH-1 downto 0);
    signal misc_out               : std_logic_vector(MISC_OUT_WIDTH-1 downto 0);

    signal pcie_clk               : std_logic;
    signal pcie_reset             : std_logic;

begin
    -- Keep I2C in high impedance
    SI5397A_I2C_SCL <= 'Z';
    SI5397A_I2C_SDA <= 'Z';

    -- Make sure the external oscillator is running
    SI5397A_OE_n    <= '0';
    SI5397A_RST_n   <= '1';

    ag_i : entity work.FPGA_COMMON
    generic map (
        PCIE_CONS               => PCIE_CONS,
        PCIE_LANES              => PCIE_LANES,
        PCIE_CLKS               => PCIE_CLKS,

        ETH_CORE_ARCH           => NET_MOD_ARCH,
        ETH_PORTS               => ETH_PORTS,
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
        PCIE_ENDPOINT_MODE      => PCIE_ENDPOINT_MODE
    )
    port map(
        SYSCLK                  => AG_SYSCLK1_P,
        SYSRST                  => '0',

        PCIE_SYSCLK_P   => PCIE_CLK1_P & PCIE_CLK0_P,
        PCIE_SYSCLK_N   => (others => '0'),
        PCIE_SYSRST_N   => (others => PCIE_PERST_N),

        PCIE_RX_P   => PCIE_RX_P,
        PCIE_RX_N   => PCIE_RX_N,

        PCIE_TX_P   => PCIE_TX_P,
        PCIE_TX_N   => PCIE_TX_N,

        ETH_REFCLK_P(0)         => QSFP_REFCLK0_P,
        ETH_REFCLK_N(0)         => '0',
        ETH_RX_P                => QSFP_RX_P,
        ETH_RX_N                => QSFP_RX_N,
        ETH_TX_P                => QSFP_TX_P,
        ETH_TX_N                => QSFP_TX_N,

        QSFP_I2C_SCL(0)         => QSFP_I2C_SCL,
        QSFP_I2C_SDA(0)         => QSFP_I2C_SDA,

        QSFP_MODSEL_N(0)        => QSFP_MODSEL_N,
        QSFP_LPMODE(0)          => QSFP_INITMODE,
        QSFP_RESET_N(0)         => QSFP_RST_N,
        QSFP_MODPRS_N(0)        => QSFP_MODPRS_N,
        QSFP_INT_N(0)           => QSFP_INT_N,

        MEM_CLK                 => mem_clk,
        MEM_RST                 => not mem_rst_n_reg,

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

        STATUS_LED_G            => open,
        STATUS_LED_R            => open,

        PCIE_CLK                => pcie_clk,
        PCIE_RESET              => pcie_reset,

        MISC_IN                 => misc_in,
        MISC_OUT                => misc_out
    );

    -- ---------------------------------------------------------------------------
    --  SODIMM Memory modules available on the Card (DDR4)
    -- ---------------------------------------------------------------------------
    sodimm_ddr4_g: if MEM_PORTS = 4 generate
        -- Registers to ensure that the reset meets the timing constraints
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
                ADATAIN  => mem_rst_n(i),
                BDATAOUT => mem_rst_n_reg(i)
            );
        end generate;

        -- DDR4A - HPS compatible
        -- This IP core enables usage of DDR4 in non-HPS system
        sodimm_hps_i : component sodimm_hps
        port map (
            local_reset_req           => emif_rst_req(0),
            local_reset_done          => emif_rst_done(0),
            pll_ref_clk               => SODIMM_HPS_REFCLK_P,
            oct_rzqin                 => SODIMM_HPS_OCT_RZQ,
            mem_ck(0)                 => SODIMM_HPS_PCK,
            mem_ck_n(0)               => SODIMM_HPS_NCK,
            mem_a                     => SODIMM_HPS_A,
            mem_act_n(0)              => SODIMM_HPS_NACT,
            mem_ba                    => SODIMM_HPS_BA,
            mem_bg                    => SODIMM_HPS_BG,
            mem_cke(0)                => SODIMM_HPS_CKE,
            mem_cs_n(0)               => SODIMM_HPS_NCS,
            mem_odt(0)                => SODIMM_HPS_ODT,
            mem_reset_n(0)            => SODIMM_HPS_NRST,
            mem_par(0)                => SODIMM_HPS_PAR,
            mem_alert_n(0)            => SODIMM_HPS_NALERT,
            mem_dqs                   => SODIMM_HPS_PDQS,
            mem_dqs_n                 => SODIMM_HPS_NDQS,
            mem_dq                    => SODIMM_HPS_DQ,
            mem_dbi_n                 => SODIMM_HPS_DM_DBI,

            emif_usr_reset_n          => mem_rst_n(0),
            emif_usr_clk              => mem_clk(0),

            amm_ready_0               => mem_avmm_ready(0),
            amm_read_0                => mem_avmm_read(0),
            amm_write_0               => mem_avmm_write(0),
            amm_address_0             => mem_avmm_address(0),
            amm_readdata_0            => mem_avmm_readdata(0),
            amm_writedata_0           => mem_avmm_writedata(0),
            amm_burstcount_0          => mem_avmm_burstcount(0),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(0),
            amm_byteenable_0          => (others => '1'),

            local_cal_success         => emif_cal_success(0),
            local_cal_fail            => emif_cal_fail(0),

            calbus_read               => calbus_read(0),
            calbus_write              => calbus_write(0),
            calbus_address            => calbus_address(0),
            calbus_wdata              => calbus_wdata(0),
            calbus_rdata              => calbus_rdata(0),
            calbus_seq_param_tbl      => calbus_seq_param_tbl(0),
            calbus_clk                => calbus_clk(0),

            ctrl_ecc_user_interrupt_0 => open
        );

        -- DDR4B
        sodimm0_i : component sodimm
        port map (
            local_reset_req           => emif_rst_req(1),
            local_reset_done          => emif_rst_done(1),
            pll_ref_clk               => SODIMM0_REFCLK_P,
            oct_rzqin                 => SODIMM0_OCT_RZQ,
            mem_ck(0)                 => SODIMM0_PCK,
            mem_ck_n(0)               => SODIMM0_NCK,
            mem_a                     => SODIMM0_A,
            mem_act_n(0)              => SODIMM0_NACT,
            mem_ba                    => SODIMM0_BA,
            mem_bg                    => SODIMM0_BG,
            mem_cke(0)                => SODIMM0_CKE,
            mem_cs_n(0)               => SODIMM0_NCS,
            mem_odt(0)                => SODIMM0_ODT,
            mem_reset_n(0)            => SODIMM0_NRST,
            mem_par(0)                => SODIMM0_PAR,
            mem_alert_n(0)            => SODIMM0_NALERT,
            mem_dqs                   => SODIMM0_PDQS,
            mem_dqs_n                 => SODIMM0_NDQS,
            mem_dq                    => SODIMM0_DQ,
            mem_dbi_n                 => SODIMM0_DM_DBI,

            emif_usr_reset_n          => mem_rst_n(1),
            emif_usr_clk              => mem_clk(1),

            amm_ready_0               => mem_avmm_ready(1),
            amm_read_0                => mem_avmm_read(1),
            amm_write_0               => mem_avmm_write(1),
            amm_address_0             => mem_avmm_address(1),
            amm_readdata_0            => mem_avmm_readdata(1),
            amm_writedata_0           => mem_avmm_writedata(1),
            amm_burstcount_0          => mem_avmm_burstcount(1),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(1),
            amm_byteenable_0          => (others => '1'),

            local_cal_success         => emif_cal_success(1),
            local_cal_fail            => emif_cal_fail(1),

            calbus_read               => calbus_read(1),
            calbus_write              => calbus_write(1),
            calbus_address            => calbus_address(1),
            calbus_wdata              => calbus_wdata(1),
            calbus_rdata              => calbus_rdata(1),
            calbus_seq_param_tbl      => calbus_seq_param_tbl(1),
            calbus_clk                => calbus_clk(0),

            ctrl_ecc_user_interrupt_0 => open
        );

        -- DDR4C
        sodimm1_i : component sodimm
        port map (
            local_reset_req           => emif_rst_req(2),
            local_reset_done          => emif_rst_done(2),
            pll_ref_clk               => SODIMM1_REFCLK_P,
            oct_rzqin                 => SODIMM1_OCT_RZQ,
            mem_ck(0)                 => SODIMM1_PCK,
            mem_ck_n(0)               => SODIMM1_NCK,
            mem_a                     => SODIMM1_A,
            mem_act_n(0)              => SODIMM1_NACT,
            mem_ba                    => SODIMM1_BA,
            mem_bg                    => SODIMM1_BG,
            mem_cke(0)                => SODIMM1_CKE,
            mem_cs_n(0)               => SODIMM1_NCS,
            mem_odt(0)                => SODIMM1_ODT,
            mem_reset_n(0)            => SODIMM1_NRST,
            mem_par(0)                => SODIMM1_PAR,
            mem_alert_n(0)            => SODIMM1_NALERT,
            mem_dqs                   => SODIMM1_PDQS,
            mem_dqs_n                 => SODIMM1_NDQS,
            mem_dq                    => SODIMM1_DQ,
            mem_dbi_n                 => SODIMM1_DM_DBI,

            emif_usr_reset_n          => mem_rst_n(2),
            emif_usr_clk              => mem_clk(2),

            amm_ready_0               => mem_avmm_ready(2),
            amm_read_0                => mem_avmm_read(2),
            amm_write_0               => mem_avmm_write(2),
            amm_address_0             => mem_avmm_address(2),
            amm_readdata_0            => mem_avmm_readdata(2),
            amm_writedata_0           => mem_avmm_writedata(2),
            amm_burstcount_0          => mem_avmm_burstcount(2),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(2),
            amm_byteenable_0          => (others => '1'),

            local_cal_success         => emif_cal_success(2),
            local_cal_fail            => emif_cal_fail(2),

            calbus_read               => calbus_read(2),
            calbus_write              => calbus_write(2),
            calbus_address            => calbus_address(2),
            calbus_wdata              => calbus_wdata(2),
            calbus_rdata              => calbus_rdata(2),
            calbus_seq_param_tbl      => calbus_seq_param_tbl(2),
            calbus_clk                => calbus_clk(1),

            ctrl_ecc_user_interrupt_0 => open
        );

        -- DDR4D
        sodimm2_i : component sodimm
        port map (
            local_reset_req           => emif_rst_req(3),
            local_reset_done          => emif_rst_done(3),
            pll_ref_clk               => SODIMM2_REFCLK_P,
            oct_rzqin                 => SODIMM2_OCT_RZQ,
            mem_ck(0)                 => SODIMM2_PCK,
            mem_ck_n(0)               => SODIMM2_NCK,
            mem_a                     => SODIMM2_A,
            mem_act_n(0)              => SODIMM2_NACT,
            mem_ba                    => SODIMM2_BA,
            mem_bg                    => SODIMM2_BG,
            mem_cke(0)                => SODIMM2_CKE,
            mem_cs_n(0)               => SODIMM2_NCS,
            mem_odt(0)                => SODIMM2_ODT,
            mem_reset_n(0)            => SODIMM2_NRST,
            mem_par(0)                => SODIMM2_PAR,
            mem_alert_n(0)            => SODIMM2_NALERT,
            mem_dqs                   => SODIMM2_PDQS,
            mem_dqs_n                 => SODIMM2_NDQS,
            mem_dq                    => SODIMM2_DQ,
            mem_dbi_n                 => SODIMM2_DM_DBI,

            emif_usr_reset_n          => mem_rst_n(3),
            emif_usr_clk              => mem_clk(3),

            amm_ready_0               => mem_avmm_ready(3),
            amm_read_0                => mem_avmm_read(3),
            amm_write_0               => mem_avmm_write(3),
            amm_address_0             => mem_avmm_address(3),
            amm_readdata_0            => mem_avmm_readdata(3),
            amm_writedata_0           => mem_avmm_writedata(3),
            amm_burstcount_0          => mem_avmm_burstcount(3),
            amm_readdatavalid_0       => mem_avmm_readdatavalid(3),
            amm_byteenable_0          => (others => '1'),

            local_cal_success         => emif_cal_success(3),
            local_cal_fail            => emif_cal_fail(3),

            calbus_read               => calbus_read(3),
            calbus_write              => calbus_write(3),
            calbus_address            => calbus_address(3),
            calbus_wdata              => calbus_wdata(3),
            calbus_rdata              => calbus_rdata(3),
            calbus_seq_param_tbl      => calbus_seq_param_tbl(3),
            calbus_clk                => calbus_clk(1),

            ctrl_ecc_user_interrupt_0 => open
        );

        -- Memory calibration - HPS Compatible SODIMM & SODIMM0
        sodimm_cal_AB_i : component sodimm_cal
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
            calbus_clk              => calbus_clk(0)
        );

        -- Memory calibration - SODIMM1 & SODIMM2
        sodimm_cal_CD_i : component sodimm_cal
        port map (
            calbus_read_0           => calbus_read(2),
            calbus_write_0          => calbus_write(2),
            calbus_address_0        => calbus_address(2),
            calbus_wdata_0          => calbus_wdata(2),
            calbus_rdata_0          => calbus_rdata(2),
            calbus_seq_param_tbl_0  => calbus_seq_param_tbl(2),
            calbus_read_1           => calbus_read(3),
            calbus_write_1          => calbus_write(3),
            calbus_address_1        => calbus_address(3),
            calbus_wdata_1          => calbus_wdata(3),
            calbus_rdata_1          => calbus_rdata(3),
            calbus_seq_param_tbl_1  => calbus_seq_param_tbl(3),
            calbus_clk              => calbus_clk(1)
        );
    end generate;

    -- Disable SODIMM DDR4
    sodimm_ddr4_empty_g: if MEM_PORTS /= 4 generate
        SODIMM_HPS_NACT   <= 'Z';
        SODIMM_HPS_NRST   <= 'Z';
        SODIMM_HPS_PAR    <= 'Z';
        SODIMM_HPS_PCK    <= 'Z';
        SODIMM_HPS_NCK    <= 'Z';
        SODIMM_HPS_A      <= (others => 'Z');
        SODIMM_HPS_BA     <= (others => 'Z');
        SODIMM_HPS_BG     <= (others => 'Z');
        SODIMM_HPS_CKE    <= 'Z';
        SODIMM_HPS_NCS    <= 'Z';
        SODIMM_HPS_ODT    <= 'Z';
        SODIMM_HPS_PDQS   <= (others => 'Z');
        SODIMM_HPS_NDQS   <= (others => 'Z');
        SODIMM_HPS_DM_DBI <= (others => 'Z');
        SODIMM_HPS_DQ     <= (others => 'Z');

        SODIMM0_NACT   <= 'Z';
        SODIMM0_NRST   <= 'Z';
        SODIMM0_PAR    <= 'Z';
        SODIMM0_PCK    <= 'Z';
        SODIMM0_NCK    <= 'Z';
        SODIMM0_A      <= (others => 'Z');
        SODIMM0_BA     <= (others => 'Z');
        SODIMM0_BG     <= (others => 'Z');
        SODIMM0_CKE    <= 'Z';
        SODIMM0_NCS    <= 'Z';
        SODIMM0_ODT    <= 'Z';
        SODIMM0_PDQS   <= (others => 'Z');
        SODIMM0_NDQS   <= (others => 'Z');
        SODIMM0_DM_DBI <= (others => 'Z');
        SODIMM0_DQ     <= (others => 'Z');

        SODIMM1_NACT   <= 'Z';
        SODIMM1_NRST   <= 'Z';
        SODIMM1_PAR    <= 'Z';
        SODIMM1_PCK    <= 'Z';
        SODIMM1_NCK    <= 'Z';
        SODIMM1_A      <= (others => 'Z');
        SODIMM1_BA     <= (others => 'Z');
        SODIMM1_BG     <= (others => 'Z');
        SODIMM1_CKE    <= 'Z';
        SODIMM1_NCS    <= 'Z';
        SODIMM1_ODT    <= 'Z';
        SODIMM1_PDQS   <= (others => 'Z');
        SODIMM1_NDQS   <= (others => 'Z');
        SODIMM1_DM_DBI <= (others => 'Z');
        SODIMM1_DQ     <= (others => 'Z');

        SODIMM2_NACT   <= 'Z';
        SODIMM2_NRST   <= 'Z';
        SODIMM2_PAR    <= 'Z';
        SODIMM2_PCK    <= 'Z';
        SODIMM2_NCK    <= 'Z';
        SODIMM2_A      <= (others => 'Z');
        SODIMM2_BA     <= (others => 'Z');
        SODIMM2_BG     <= (others => 'Z');
        SODIMM2_CKE    <= 'Z';
        SODIMM2_NCS    <= 'Z';
        SODIMM2_ODT    <= 'Z';
        SODIMM2_PDQS   <= (others => 'Z');
        SODIMM2_NDQS   <= (others => 'Z');
        SODIMM2_DM_DBI <= (others => 'Z');
        SODIMM2_DQ     <= (others => 'Z');
    end generate;

end architecture;
