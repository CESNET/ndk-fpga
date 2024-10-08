-- fpga.vhd: IA-420F board top level entity and architecture
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz.cz>
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
    USR_CLK_33M        : in    std_logic;
    SYS_CLK_50M        : in    std_logic;
    -- User LEDs
    USER_LED_G         : out   std_logic;
    USER_LED_R         : out   std_logic;

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
    QSFP_REFCLK_156M   : in    std_logic;
    QSFP_RX_P          : in    std_logic_vector(8-1 downto 0);
    QSFP_RX_N          : in    std_logic_vector(8-1 downto 0);
    QSFP_TX_P          : out   std_logic_vector(8-1 downto 0);
    QSFP_TX_N          : out   std_logic_vector(8-1 downto 0);

    -- =========================================================================
    -- DDR4 PORT0
    -- =========================================================================
    P0_DDR4_REFCLK       : in    std_logic;
    P0_DDR4_CLK_P        : out   std_logic_vector(0 downto 0);
    P0_DDR4_CLK_N        : out   std_logic_vector(0 downto 0);
    P0_DDR4_A            : out   std_logic_vector(16 downto 0);
    P0_DDR4_ACT_L        : out   std_logic_vector(0 downto 0);
    P0_DDR4_BA           : out   std_logic_vector(1 downto 0);
    P0_DDR4_BG           : out   std_logic_vector(1 downto 0);
    P0_DDR4_CKE          : out   std_logic_vector(0 downto 0);
    P0_DDR4_CS_L         : out   std_logic_vector(0 downto 0);
    P0_DDR4_ODT          : out   std_logic_vector(0 downto 0);
    P0_DDR4_RESET_L      : out   std_logic_vector(0 downto 0);
    P0_DDR4_PARITY       : out   std_logic_vector(0 downto 0);
    P0_DDR4_ALERT_L      : in    std_logic_vector(0 downto 0);
    P0_DDR4_DM           : inout std_logic_vector(8 downto 0);
    P0_DDR4_DQS_P        : inout std_logic_vector(8 downto 0);
    P0_DDR4_DQS_N        : inout std_logic_vector(8 downto 0);
    P0_DDR4_DQ           : inout std_logic_vector(71 downto 0);
    P0_RZQ               : in    std_logic;

    -- =========================================================================
    -- DDR4 PORT1
    -- =========================================================================
    P1_DDR4_REFCLK       : in    std_logic;
    P1_DDR4_CLK_P        : out   std_logic_vector(0 downto 0);
    P1_DDR4_CLK_N        : out   std_logic_vector(0 downto 0);
    P1_DDR4_A            : out   std_logic_vector(16 downto 0);
    P1_DDR4_ACT_L        : out   std_logic_vector(0 downto 0);
    P1_DDR4_BA           : out   std_logic_vector(1 downto 0);
    P1_DDR4_BG           : out   std_logic_vector(1 downto 0);
    P1_DDR4_CKE          : out   std_logic_vector(0 downto 0);
    P1_DDR4_CS_L         : out   std_logic_vector(0 downto 0);
    P1_DDR4_ODT          : out   std_logic_vector(0 downto 0);
    P1_DDR4_RESET_L      : out   std_logic_vector(0 downto 0);
    P1_DDR4_PARITY       : out   std_logic_vector(0 downto 0);
    P1_DDR4_ALERT_L      : in    std_logic_vector(0 downto 0);
    P1_DDR4_DM           : inout std_logic_vector(8 downto 0);
    P1_DDR4_DQS_P        : inout std_logic_vector(8 downto 0);
    P1_DDR4_DQS_N        : inout std_logic_vector(8 downto 0);
    P1_DDR4_DQ           : inout std_logic_vector(71 downto 0);
    P1_RZQ               : in    std_logic;  
  
    -- =========================================================================
    -- I2C
    -- =========================================================================
    FPGA_I2C_SCL         : inout std_logic;
    FPGA_I2C_SDA         : inout std_logic;
    FPGA_I2C_MUX_GNT     : in    std_logic;
    FPGA_I2C_REQ_L       : out   std_logic;

    -- =========================================================================
    -- BMC SPI
    -- =========================================================================
    FPGA2BMC_IRQ         : out   std_logic;
    FPGA2BMC_MST_EN_N    : out   std_logic;
    BMC2FPGA_RST_N       : in    std_logic;
    BMC2FPGA_SPI_SCK     : in    std_logic;
    BMC2FPGA_SPI_MOSI    : in    std_logic;
    BMC2FPGA_SPI_CS      : in    std_logic;
    BMC2FPGA_SPI_MISO    : inout std_logic
);
end entity;

architecture FULL of FPGA is

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
        mem_bg               : out   std_logic_vector(1 downto 0);                       -- mem_bg
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
        local_reset_req                 : in    std_logic                       := 'X';             -- local_reset_req
        local_reset_done                : out   std_logic;                                          -- local_reset_done
        pll_ref_clk                     : in    std_logic                       := 'X';             -- clk
        pll_ref_clk_out                 : out   std_logic;                                          -- clk
        pll_locked                      : out   std_logic;                                          -- pll_locked
        oct_rzqin                       : in    std_logic                       := 'X';             -- oct_rzqin
        mem_ck                          : out   std_logic_vector(0 downto 0);                       -- mem_ck
        mem_ck_n                        : out   std_logic_vector(0 downto 0);                       -- mem_ck_n
        mem_a                           : out   std_logic_vector(16 downto 0);                      -- mem_a
        mem_act_n                       : out   std_logic_vector(0 downto 0);                       -- mem_act_n
        mem_ba                          : out   std_logic_vector(1 downto 0);                       -- mem_ba
        mem_bg                          : out   std_logic_vector(1 downto 0);                       -- mem_bg
        mem_cke                         : out   std_logic_vector(0 downto 0);                       -- mem_cke
        mem_cs_n                        : out   std_logic_vector(0 downto 0);                       -- mem_cs_n
        mem_odt                         : out   std_logic_vector(0 downto 0);                       -- mem_odt
        mem_reset_n                     : out   std_logic_vector(0 downto 0);                       -- mem_reset_n
        mem_par                         : out   std_logic_vector(0 downto 0);                       -- mem_par
        mem_alert_n                     : in    std_logic_vector(0 downto 0)    := (others => 'X'); -- mem_alert_n
        mem_dqs                         : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs
        mem_dqs_n                       : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dqs_n
        mem_dq                          : inout std_logic_vector(71 downto 0)   := (others => 'X'); -- mem_dq
        mem_dbi_n                       : inout std_logic_vector(8 downto 0)    := (others => 'X'); -- mem_dbi_n
        local_cal_success               : out   std_logic;                                          -- local_cal_success
        local_cal_fail                  : out   std_logic;                                          -- local_cal_fail
        calbus_read                     : in    std_logic                       := 'X';             -- calbus_read
        calbus_write                    : in    std_logic                       := 'X';             -- calbus_write
        calbus_address                  : in    std_logic_vector(19 downto 0)   := (others => 'X'); -- calbus_address
        calbus_wdata                    : in    std_logic_vector(31 downto 0)   := (others => 'X'); -- calbus_wdata
        calbus_rdata                    : out   std_logic_vector(31 downto 0);                      -- calbus_rdata
        calbus_seq_param_tbl            : out   std_logic_vector(4095 downto 0);                    -- calbus_seq_param_tbl
        calbus_clk                      : in    std_logic                       := 'X';             -- clk
        emif_usr_reset_n                : out   std_logic;                                          -- reset_n
        emif_usr_clk                    : out   std_logic;                                          -- clk
        ctrl_ecc_user_interrupt_0       : out   std_logic;                                          -- ctrl_ecc_user_interrupt
        ctrl_ecc_readdataerror_0        : out   std_logic;                                          -- ctrl_ecc_readdataerror
        ctrl_ecc_sts_intr               : out   std_logic_vector(0 downto 0);                       -- ctrl_ecc_sts_intr
        ctrl_ecc_sts_sbe_error          : out   std_logic_vector(0 downto 0);                       -- ctrl_ecc_sts_sbe_error
        ctrl_ecc_sts_dbe_error          : out   std_logic_vector(0 downto 0);                       -- ctrl_ecc_sts_dbe_error
        ctrl_ecc_sts_corr_dropped       : out   std_logic_vector(0 downto 0);                       -- ctrl_ecc_sts_corr_dropped
        ctrl_ecc_sts_sbe_count          : out   std_logic_vector(3 downto 0);                       -- ctrl_ecc_sts_sbe_count
        ctrl_ecc_sts_dbe_count          : out   std_logic_vector(3 downto 0);                       -- ctrl_ecc_sts_dbe_count
        ctrl_ecc_sts_corr_dropped_count : out   std_logic_vector(3 downto 0);                       -- ctrl_ecc_sts_corr_dropped_count
        ctrl_ecc_sts_err_addr           : out   std_logic_vector(34 downto 0);                      -- ctrl_ecc_sts_err_addr
        ctrl_ecc_sts_corr_dropped_addr  : out   std_logic_vector(34 downto 0);                      -- ctrl_ecc_sts_corr_dropped_addr
        amm_ready_0                     : out   std_logic;                                          -- waitrequest_n
        amm_read_0                      : in    std_logic                       := 'X';             -- read
        amm_write_0                     : in    std_logic                       := 'X';             -- write
        amm_address_0                   : in    std_logic_vector(26 downto 0)   := (others => 'X'); -- address
        amm_readdata_0                  : out   std_logic_vector(511 downto 0);                     -- readdata
        amm_writedata_0                 : in    std_logic_vector(511 downto 0)  := (others => 'X'); -- writedata
        amm_burstcount_0                : in    std_logic_vector(6 downto 0)    := (others => 'X'); -- burstcount
        amm_byteenable_0                : in    std_logic_vector(63 downto 0)   := (others => 'X'); -- byteenable
        amm_readdatavalid_0             : out   std_logic                                           -- readdatavalid
    );
    end component;

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

    constant PCIE_LANES      : natural := 16;
    constant PCIE_CLKS       : natural := 2;
    constant PCIE_CONS       : natural := 1;
    constant MISC_IN_WIDTH   : natural := 4;
    constant MISC_OUT_WIDTH  : natural := 4;
    constant ETH_LANES       : natural := 4;
    constant DMA_MODULES     : natural := ETH_PORTS;
    constant DMA_ENDPOINTS   : natural := tsel(PCIE_ENDPOINT_MODE=1,PCIE_ENDPOINTS,2*PCIE_ENDPOINTS);
    constant STATUS_LEDS     : natural := 4;

    constant MEM_PORTS       : natural := 2;
    constant MEM_ADDR_WIDTH  : natural := 27;
    constant MEM_DATA_WIDTH  : natural := 512;
    constant MEM_BURST_WIDTH : natural := 7;
    constant AMM_FREQ_KHZ    : natural := 333333;

    signal status_led_g           : std_logic_vector(STATUS_LEDS-1 downto 0);
    signal status_led_r           : std_logic_vector(STATUS_LEDS-1 downto 0);  
    -- IO Expander
    signal io_reset               : std_logic;
    signal io_reset_sync          : std_logic;
    signal ioexp_o                : std_logic_vector(8-1 downto 0);
    signal ioexp_i                : std_logic_vector(8-1 downto 0);
    signal ioexp_req              : std_logic;
    signal ioexp_gnt              : std_logic;
    signal ioexp_busy             : std_logic;
    signal ioexp_done             : std_logic;
    signal sda_o                  : std_logic;
    signal sda_oen                : std_logic;
    signal scl_o                  : std_logic;
    signal scl_oen                : std_logic;
    -- QSFP I2C
    signal qsfp_sda               : std_logic;
    signal qsfp_scl               : std_logic;
    signal qsfp_sda_o             : std_logic;
    signal qsfp_scl_o             : std_logic;
    signal qsfp_sda_oe            : std_logic;
    signal qsfp_scl_oe            : std_logic;
    -- I2C arbitration
    signal qsfp_idle_timer        : unsigned(12 downto 0); -- 80 us timer
    signal qsfp_scl_oe_sync       : std_logic;
    signal qsfp_i2c_idle          : std_logic;

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
    signal mem_avmm_readdata_full : slv_array_t(MEM_PORTS-1 downto 0)(576-1 downto 0);
    signal mem_avmm_readdatavalid : std_logic_vector(MEM_PORTS-1 downto 0);
     
    signal emif_rst_req           : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_ecc_usr_int       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_success       : std_logic_vector(MEM_PORTS-1 downto 0);
    signal emif_cal_fail          : std_logic_vector(MEM_PORTS-1 downto 0);

begin

    FPGA_I2C_REQ_L    <= '0';

    FPGA2BMC_IRQ      <= '1';
    FPGA2BMC_MST_EN_N <= '1';
    BMC2FPGA_SPI_MISO <= '1';

    ioreset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => SYS_CLK_50M,
        ASYNC_RST  => io_reset,
        OUT_RST(0) => io_reset_sync
    );

    -- TCS5455 IO expander for QSFP control
    -- O(4): lp_mode; O(7): reset_n; I(5): int_n, I(6): mod_prs_n
    i2c_io_exp_i: entity work.i2c_io_exp
    generic map (
        IIC_CLK_CNT    => X"0080",   -- Clock dividier
        IIC_DEV_ADDR   => "0100000", -- 0x20
        REFRESH_CYCLES => 16#100000# -- ~21 ms @ 50 MHz
    )
    port map (
        --
        RESET      => io_reset_sync,
        CLK        => SYS_CLK_50M,
        -- Remote I/O interface
        DIR        => "01100000",
        O          => ioexp_o,
        I          => ioexp_i,
        -- Control
        REFRESH    => '0', -- Do not refresh maually, use auto-refresh each REFRESH_CYCLES
        CONFIG     => '0', -- Do not configure maually, config on powerup and when DIR or O port changes
        ERROR      => open,
        -- I2C bus arbitration
        I2C_REQ    => ioexp_req,
        I2C_GNT    => ioexp_gnt,
        I2C_BUSY   => ioexp_busy,
        I2C_DONE   => ioexp_done,
        -- I2C interface
        SCL_I      => FPGA_I2C_SCL,
        SCL_O      => scl_o,
        SCL_OEN    => scl_oen,
        SDA_I      => FPGA_I2C_SDA,
        SDA_O      => sda_o,
        SDA_OEN    => sda_oen
    );

    sync_qsfp_i2c_i: entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG   => false,
        TWO_REG  => true
    )
    port map (
        ADATAIN  => qsfp_scl_oe,
        BCLK     => SYS_CLK_50M,
        BDATAOUT => qsfp_scl_oe_sync
    );
    --
    arbit_p: process(SYS_CLK_50M)
    begin
        if rising_edge(SYS_CLK_50M) then
            if (ioexp_req = '1') and (qsfp_i2c_idle = '1') then
                ioexp_gnt <= not FPGA_I2C_MUX_GNT;
            elsif ioexp_done = '1' then
                ioexp_gnt <= '0';
            end if;
            -- Detect activity on QSFP I2C
            if qsfp_scl_oe_sync = '1' then
                qsfp_idle_timer <= (others => '0');
            elsif qsfp_idle_timer(qsfp_idle_timer'high) = '0' then
                qsfp_idle_timer <= qsfp_idle_timer + 1;
            end if;
        end if;
    end process;

    qsfp_i2c_idle <= qsfp_idle_timer(qsfp_idle_timer'high);

    FPGA_I2C_SCL <= scl_o      when (scl_oen = '0' and ioexp_busy = '1')     else
                    qsfp_scl_o when (qsfp_scl_oe = '1' and ioexp_busy = '0') else
                   'Z';

    FPGA_I2C_SDA <= sda_o      when (sda_oen = '0' and ioexp_busy = '1')     else
                    qsfp_sda_o when (qsfp_sda_oe = '1' and ioexp_busy = '0') else
                   'Z';

    -- Clock stretching - hold SCL low when the bus is busy
    qsfp_scl <= '0' when (ioexp_busy = '1') else FPGA_I2C_SCL;
    qsfp_sda <= '0' when (ioexp_busy = '1') else FPGA_I2C_SDA;

    cm_i : entity work.FPGA_COMMON
    generic map (
        SYSCLK_PERIOD           => 20.0,
        PLL_MULT_F              => 24.0,
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
        ETH_PORTS               => ETH_PORTS, -- one QSFP-DD cage as two ETH ports
        ETH_PORT_SPEED          => ETH_PORT_SPEED,
        ETH_PORT_CHAN           => ETH_PORT_CHAN,
        ETH_PORT_LEDS           => 1, -- fake, this board has no ETH LEDs
        ETH_LANES               => ETH_LANES,
        
        QSFP_PORTS              => 1,
        QSFP_I2C_PORTS          => 1,
        QSFP_I2C_TRISTATE       => false,

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
        SYSCLK                 => SYS_CLK_50M,
        SYSRST                 => '0',

        PCIE_SYSCLK_P          => PCIE_REFCLK1 & PCIE_REFCLK0,
        PCIE_SYSCLK_N          => (others => '0'),
        PCIE_SYSRST_N(0)       => PCIE_SYSRST_N,

        PCIE_RX_P              => PCIE_RX_P,
        PCIE_RX_N              => PCIE_RX_N,
        PCIE_TX_P              => PCIE_TX_P,
        PCIE_TX_N              => PCIE_TX_N,
        
        ETH_REFCLK_P           => QSFP_REFCLK_156M & QSFP_REFCLK_156M,
        ETH_REFCLK_N           => (others => '0'),
        
        ETH_RX_P               => QSFP_RX_P,
        ETH_RX_N               => QSFP_RX_N,
        ETH_TX_P               => QSFP_TX_P,
        ETH_TX_N               => QSFP_TX_N,

        ETH_LED_R              => open,
        ETH_LED_G              => open,
        
        QSFP_I2C_SCL_I(0)      => qsfp_scl,
        QSFP_I2C_SDA_I(0)      => qsfp_sda,
        QSFP_I2C_SCL_O(0)      => qsfp_scl_o,
        QSFP_I2C_SCL_OE(0)     => qsfp_scl_oe,
        QSFP_I2C_SDA_O(0)      => qsfp_sda_o,
        QSFP_I2C_SDA_OE(0)     => qsfp_sda_oe,

        QSFP_MODSEL_N          => open,
        QSFP_LPMODE(0)         => ioexp_o(4),
        QSFP_RESET_N(0)        => ioexp_o(7),
        QSFP_MODPRS_N          => (others => ioexp_i(6)),
        QSFP_INT_N             => (others => ioexp_i(5)),

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
        BOOT_MI_RESET          => io_reset,

        STATUS_LED_G           => status_led_g,
        STATUS_LED_R           => status_led_r,

        MISC_IN                => (others => '0'),
        MISC_OUT               => open
    );

    USER_LED_G <= status_led_g(0);
    USER_LED_R <= status_led_r(0);

    ddr4_p0_i : component onboard_ddr4_0
    port map (
        local_reset_req      => emif_rst_req(0),
        local_reset_done     => emif_rst_done(0),
        pll_ref_clk          => P0_DDR4_REFCLK,
        pll_ref_clk_out      => open,
        pll_locked           => mem_pll_locked(0),
        oct_rzqin            => P0_RZQ,
        mem_ck               => P0_DDR4_CLK_P,
        mem_ck_n             => P0_DDR4_CLK_N,
        mem_a                => P0_DDR4_A,
        mem_act_n            => P0_DDR4_ACT_L,
        mem_ba               => P0_DDR4_BA,
        mem_bg               => P0_DDR4_BG,
        mem_cke              => P0_DDR4_CKE,
        mem_cs_n             => P0_DDR4_CS_L,
        mem_odt              => P0_DDR4_ODT,
        mem_reset_n          => P0_DDR4_RESET_L,
        mem_par              => P0_DDR4_PARITY,
        mem_alert_n          => P0_DDR4_ALERT_L,
        mem_dqs              => P0_DDR4_DQS_P,
        mem_dqs_n            => P0_DDR4_DQS_N,
        mem_dq               => P0_DDR4_DQ,
        mem_dbi_n            => P0_DDR4_DM,
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
        calbus_read_0               => calbus_read(0),              
        calbus_write_0              => calbus_write(0),       
        calbus_address_0            => calbus_address(0),     
        calbus_wdata_0              => calbus_wdata(0),    
        calbus_rdata_0              => calbus_rdata(0),       
        calbus_seq_param_tbl_0      => calbus_seq_param_tbl(0),
        calbus_clk                  => calbus_clk(0)
    );

    ddr4_p1_i : component onboard_ddr4_1
    port map (
        local_reset_req      => emif_rst_req(1),
        local_reset_done     => emif_rst_done(1),
        pll_ref_clk          => P1_DDR4_REFCLK,
        pll_ref_clk_out      => open,
        pll_locked           => mem_pll_locked(1),
        oct_rzqin            => P1_RZQ,
        mem_ck               => P1_DDR4_CLK_P,
        mem_ck_n             => P1_DDR4_CLK_N,
        mem_a                => P1_DDR4_A,
        mem_act_n            => P1_DDR4_ACT_L,
        mem_ba               => P1_DDR4_BA,
        mem_bg               => P1_DDR4_BG,
        mem_cke              => P1_DDR4_CKE,
        mem_cs_n             => P1_DDR4_CS_L,
        mem_odt              => P1_DDR4_ODT,
        mem_reset_n          => P1_DDR4_RESET_L,
        mem_par              => P1_DDR4_PARITY,
        mem_alert_n          => P1_DDR4_ALERT_L,
        mem_dqs              => P1_DDR4_DQS_P,
        mem_dqs_n            => P1_DDR4_DQS_N,
        mem_dq               => P1_DDR4_DQ,
        mem_dbi_n            => P1_DDR4_DM,
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
        calbus_read_0               => calbus_read(1),              
        calbus_write_0              => calbus_write(1),       
        calbus_address_0            => calbus_address(1),     
        calbus_wdata_0              => calbus_wdata(1),    
        calbus_rdata_0              => calbus_rdata(1),       
        calbus_seq_param_tbl_0      => calbus_seq_param_tbl(1),
        calbus_clk                  => calbus_clk(1)
    );

end architecture;
