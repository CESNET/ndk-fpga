-- fpga.vhd: N5014 board top level entity and architecture
-- Copyright (C) 2023 CESNET z. s. p. o.
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
    ETILE_REFCLK_156M    : in   std_logic;

    -- QSFP data
    QSFP0_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP0_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP0_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP0_TX_N          : out   std_logic_vector(4-1 downto 0);

    QSFP1_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP1_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP1_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP1_TX_N          : out   std_logic_vector(4-1 downto 0);

    QSFP2_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP2_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP2_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP2_TX_N          : out   std_logic_vector(4-1 downto 0);

    QSFP3_RX_P          : in    std_logic_vector(4-1 downto 0);
    QSFP3_RX_N          : in    std_logic_vector(4-1 downto 0);
    QSFP3_TX_P          : out   std_logic_vector(4-1 downto 0);
    QSFP3_TX_N          : out   std_logic_vector(4-1 downto 0);

    -- =========================================================================
    -- DDR4
    -- =========================================================================

    DDR4_CH0_REF_CLK   : in    std_logic;
    DDR4_CH0_CK_P      : out   std_logic_vector(0 downto 0);
    DDR4_CH0_CK_N      : out   std_logic_vector(0 downto 0);
    DDR4_CH0_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH0_ACT_N     : out   std_logic;
    DDR4_CH0_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH0_BG        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH0_CKE       : out   std_logic_vector(0 downto 0);
    DDR4_CH0_CS_N      : out   std_logic_vector(0 downto 0);
    DDR4_CH0_ODT       : out   std_logic_vector(0 downto 0);
    DDR4_CH0_RESET_N   : out   std_logic;
    DDR4_CH0_PAR       : out   std_logic;
    DDR4_CH0_ALERT_N   : in    std_logic;
    DDR4_CH0_DQS_P     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH0_DQS_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH0_DBI_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH0_DQ        : inout std_logic_vector(72-1 downto 0);
    --DDR4_CH0_RZQ       : inout std_logic;
    DDR4_CH0_RZQ       : in    std_logic;

    DDR4_CH1_REF_CLK   : in    std_logic;
    DDR4_CH1_CK_P      : out   std_logic_vector(0 downto 0);
    DDR4_CH1_CK_N      : out   std_logic_vector(0 downto 0);
    DDR4_CH1_A         : out   std_logic_vector(17-1 downto 0);
    DDR4_CH1_ACT_N     : out   std_logic;
    DDR4_CH1_BA        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH1_BG        : out   std_logic_vector(2-1 downto 0);
    DDR4_CH1_CKE       : out   std_logic_vector(0 downto 0);
    DDR4_CH1_CS_N      : out   std_logic_vector(0 downto 0);
    DDR4_CH1_ODT       : out   std_logic_vector(0 downto 0);
    DDR4_CH1_RESET_N   : out   std_logic;
    DDR4_CH1_PAR       : out   std_logic;
    DDR4_CH1_ALERT_N   : in    std_logic;
    DDR4_CH1_DQS_P     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH1_DQS_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH1_DBI_N     : inout std_logic_vector(9-1 downto 0);
    DDR4_CH1_DQ        : inout std_logic_vector(72-1 downto 0);
    --DDR4_CH1_RZQ       : inout std_logic;
    DDR4_CH1_RZQ       : in    std_logic;

    -- =========================================================================
    -- HBM
    -- =========================================================================

    HBM_TOP_REF_CLK       : in    std_logic;
    HBM_TOP_CATTRIP       : in    std_logic;
    HBM_TOP_TEMP          : in    std_logic_vector(2 downto 0);
    HBM_TOP_WSO           : in    std_logic_vector(7 downto 0);
    HBM_TOP_RESET_N       : out   std_logic;
    HBM_TOP_WRST_N        : out   std_logic;
    HBM_TOP_WRCK          : out   std_logic;
    HBM_TOP_SHIFTWR       : out   std_logic;
    HBM_TOP_CAPTUREWR     : out   std_logic;
    HBM_TOP_UPDATEWR      : out   std_logic;
    HBM_TOP_SELECTWIR     : out   std_logic;
    HBM_TOP_WSI           : out   std_logic;


    HBM_BOTTOM_REF_CLK    : in    std_logic;
    HBM_BOTTOM_CATTRIP    : in    std_logic;
    HBM_BOTTOM_TEMP       : in    std_logic_vector(2 downto 0);
    HBM_BOTTOM_WSO        : in    std_logic_vector(7 downto 0);
    HBM_BOTTOM_RESET_N    : out   std_logic;
    HBM_BOTTOM_WRST_N     : out   std_logic;
    HBM_BOTTOM_WRCK       : out   std_logic;
    HBM_BOTTOM_SHIFTWR    : out   std_logic;
    HBM_BOTTOM_CAPTUREWR  : out   std_logic;
    HBM_BOTTOM_UPDATEWR   : out   std_logic;
    HBM_BOTTOM_SELECTWIR  : out   std_logic;
    HBM_BOTTOM_WSI        : out   std_logic;

    -- =========================================================================
    -- BMC INTERFACE
    -- =========================================================================
    BMC_NINIT_DONE : out std_logic;

    SPI_SCLK : out   std_logic;
    SPI_CS_L : out   std_logic;
    SPI_MOSI : out   std_logic;
    SPI_MISO : in    std_logic
);
end entity;

architecture FULL of FPGA is

    component emif_ddr4_x64_ecc_bank0 is
    port (
        local_reset_req           : in    std_logic                      := 'X';
        local_reset_done          : out   std_logic;
        pll_ref_clk               : in    std_logic                      := 'X';
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
        amm_address_0             : in    std_logic_vector(27 downto 0)  := (others => 'X');
        amm_readdata_0            : out   std_logic_vector(511 downto 0);
        amm_writedata_0           : in    std_logic_vector(511 downto 0) := (others => 'X');
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)   := (others => 'X');
        amm_byteenable_0          : in    std_logic_vector(63 downto 0)  := (others => 'X');
        amm_readdatavalid_0       : out   std_logic
    );
    end component;

    component emif_ddr4_x64_ecc_bank1 is
    port (
        local_reset_req           : in    std_logic                      := 'X';
        local_reset_done          : out   std_logic;
        pll_ref_clk               : in    std_logic                      := 'X';
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
        amm_address_0             : in    std_logic_vector(27 downto 0)  := (others => 'X');
        amm_readdata_0            : out   std_logic_vector(511 downto 0);
        amm_writedata_0           : in    std_logic_vector(511 downto 0) := (others => 'X');
        amm_burstcount_0          : in    std_logic_vector(6 downto 0)   := (others => 'X');
        amm_byteenable_0          : in    std_logic_vector(63 downto 0)  := (others => 'X');
        amm_readdatavalid_0       : out   std_logic
    );
    end component;

    component hbm_top is
        port (
            pll_ref_clk                 : in    std_logic                      := 'X';             -- clk
            ext_core_clk                : in    std_logic                      := 'X';             -- clk
            ext_core_clk_locked         : in    std_logic                      := 'X';             -- export
            wmcrst_n_in                 : in    std_logic                      := 'X';             -- reset_n
            hbm_only_reset_in           : in    std_logic                      := 'X';             -- reset
            local_cal_success           : out   std_logic;                                         -- local_cal_success
            local_cal_fail              : out   std_logic;                                         -- local_cal_fail
            cal_lat                     : out   std_logic_vector(2 downto 0);                      -- cal_lat
            ck_t_0                      : out   std_logic;                                         -- ck_t
            ck_c_0                      : out   std_logic;                                         -- ck_c
            cke_0                       : out   std_logic;                                         -- cke
            c_0                         : out   std_logic_vector(7 downto 0);                      -- c
            r_0                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_0                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_0                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_0                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_0                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_0                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_0                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_0                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_0                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_0                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_0                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_0                        : out   std_logic;                                         -- rr
            rc_0                        : out   std_logic;                                         -- rc
            aerr_0                      : in    std_logic                      := 'X';             -- aerr
            ck_t_1                      : out   std_logic;                                         -- ck_t
            ck_c_1                      : out   std_logic;                                         -- ck_c
            cke_1                       : out   std_logic;                                         -- cke
            c_1                         : out   std_logic_vector(7 downto 0);                      -- c
            r_1                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_1                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_1                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_1                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_1                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_1                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_1                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_1                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_1                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_1                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_1                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_1                        : out   std_logic;                                         -- rr
            rc_1                        : out   std_logic;                                         -- rc
            aerr_1                      : in    std_logic                      := 'X';             -- aerr
            ck_t_2                      : out   std_logic;                                         -- ck_t
            ck_c_2                      : out   std_logic;                                         -- ck_c
            cke_2                       : out   std_logic;                                         -- cke
            c_2                         : out   std_logic_vector(7 downto 0);                      -- c
            r_2                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_2                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_2                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_2                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_2                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_2                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_2                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_2                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_2                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_2                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_2                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_2                        : out   std_logic;                                         -- rr
            rc_2                        : out   std_logic;                                         -- rc
            aerr_2                      : in    std_logic                      := 'X';             -- aerr
            ck_t_3                      : out   std_logic;                                         -- ck_t
            ck_c_3                      : out   std_logic;                                         -- ck_c
            cke_3                       : out   std_logic;                                         -- cke
            c_3                         : out   std_logic_vector(7 downto 0);                      -- c
            r_3                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_3                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_3                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_3                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_3                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_3                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_3                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_3                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_3                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_3                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_3                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_3                        : out   std_logic;                                         -- rr
            rc_3                        : out   std_logic;                                         -- rc
            aerr_3                      : in    std_logic                      := 'X';             -- aerr
            ck_t_4                      : out   std_logic;                                         -- ck_t
            ck_c_4                      : out   std_logic;                                         -- ck_c
            cke_4                       : out   std_logic;                                         -- cke
            c_4                         : out   std_logic_vector(7 downto 0);                      -- c
            r_4                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_4                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_4                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_4                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_4                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_4                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_4                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_4                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_4                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_4                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_4                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_4                        : out   std_logic;                                         -- rr
            rc_4                        : out   std_logic;                                         -- rc
            aerr_4                      : in    std_logic                      := 'X';             -- aerr
            ck_t_5                      : out   std_logic;                                         -- ck_t
            ck_c_5                      : out   std_logic;                                         -- ck_c
            cke_5                       : out   std_logic;                                         -- cke
            c_5                         : out   std_logic_vector(7 downto 0);                      -- c
            r_5                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_5                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_5                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_5                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_5                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_5                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_5                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_5                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_5                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_5                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_5                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_5                        : out   std_logic;                                         -- rr
            rc_5                        : out   std_logic;                                         -- rc
            aerr_5                      : in    std_logic                      := 'X';             -- aerr
            ck_t_6                      : out   std_logic;                                         -- ck_t
            ck_c_6                      : out   std_logic;                                         -- ck_c
            cke_6                       : out   std_logic;                                         -- cke
            c_6                         : out   std_logic_vector(7 downto 0);                      -- c
            r_6                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_6                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_6                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_6                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_6                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_6                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_6                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_6                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_6                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_6                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_6                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_6                        : out   std_logic;                                         -- rr
            rc_6                        : out   std_logic;                                         -- rc
            aerr_6                      : in    std_logic                      := 'X';             -- aerr
            ck_t_7                      : out   std_logic;                                         -- ck_t
            ck_c_7                      : out   std_logic;                                         -- ck_c
            cke_7                       : out   std_logic;                                         -- cke
            c_7                         : out   std_logic_vector(7 downto 0);                      -- c
            r_7                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_7                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_7                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_7                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_7                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_7                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_7                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_7                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_7                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_7                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_7                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_7                        : out   std_logic;                                         -- rr
            rc_7                        : out   std_logic;                                         -- rc
            aerr_7                      : in    std_logic                      := 'X';             -- aerr
            cattrip                     : in    std_logic                      := 'X';             -- cattrip
            temp                        : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- temp
            wso                         : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- wso
            reset_n                     : out   std_logic;                                         -- reset_n
            wrst_n                      : out   std_logic;                                         -- wrst_n
            wrck                        : out   std_logic;                                         -- wrck
            shiftwr                     : out   std_logic;                                         -- shiftwr
            capturewr                   : out   std_logic;                                         -- capturewr
            updatewr                    : out   std_logic;                                         -- updatewr
            selectwir                   : out   std_logic;                                         -- selectwir
            wsi                         : out   std_logic;                                         -- wsi
            wmc_clk_0_clk               : out   std_logic;                                         -- clk
            wmc_clk_1_clk               : out   std_logic;                                         -- clk
            phy_clk_0_clk               : out   std_logic;                                         -- clk
            phy_clk_1_clk               : out   std_logic;                                         -- clk
            wmcrst_n_0_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_1_reset_n          : out   std_logic;                                         -- reset_n
            axi_0_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_0_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_0_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_0_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_0_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_0_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_0_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_0_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_0_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_0_1_awready             : out   std_logic;                                         -- awready
            axi_0_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_0_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_0_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_0_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_0_1_wready              : out   std_logic;                                         -- wready
            axi_0_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_0_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_0_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_0_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_0_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_0_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_0_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_0_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_0_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_0_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_0_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_0_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_0_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_0_1_arready             : out   std_logic;                                         -- arready
            axi_0_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_0_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_0_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_0_1_rlast               : out   std_logic;                                         -- rlast
            axi_0_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_0_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_0_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_0_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_0_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_0_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_0_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_0_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_0_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_0_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_0_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_0_0_awready             : out   std_logic;                                         -- awready
            axi_0_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_0_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_0_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_0_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_0_0_wready              : out   std_logic;                                         -- wready
            axi_0_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_0_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_0_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_0_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_0_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_0_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_0_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_0_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_0_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_0_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_0_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_0_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_0_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_0_0_arready             : out   std_logic;                                         -- arready
            axi_0_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_0_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_0_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_0_0_rlast               : out   std_logic;                                         -- rlast
            axi_0_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_0_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_1_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_1_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_1_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_1_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_1_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_1_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_1_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_1_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_1_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_1_1_awready             : out   std_logic;                                         -- awready
            axi_1_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_1_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_1_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_1_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_1_1_wready              : out   std_logic;                                         -- wready
            axi_1_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_1_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_1_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_1_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_1_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_1_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_1_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_1_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_1_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_1_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_1_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_1_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_1_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_1_1_arready             : out   std_logic;                                         -- arready
            axi_1_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_1_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_1_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_1_1_rlast               : out   std_logic;                                         -- rlast
            axi_1_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_1_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_1_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_1_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_1_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_1_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_1_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_1_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_1_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_1_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_1_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_1_0_awready             : out   std_logic;                                         -- awready
            axi_1_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_1_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_1_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_1_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_1_0_wready              : out   std_logic;                                         -- wready
            axi_1_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_1_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_1_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_1_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_1_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_1_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_1_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_1_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_1_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_1_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_1_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_1_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_1_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_1_0_arready             : out   std_logic;                                         -- arready
            axi_1_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_1_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_1_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_1_0_rlast               : out   std_logic;                                         -- rlast
            axi_1_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_1_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_0_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_0_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_0_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_0_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_0_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_0_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_0_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_0_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_1_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_1_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_1_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_1_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_1_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_1_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_1_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_1_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_0_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_0_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_0_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_0_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_0_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_0_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_0_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_0_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_1_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_1_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_1_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_1_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_1_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_1_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_1_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_1_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_2_clk               : out   std_logic;                                         -- clk
            wmc_clk_3_clk               : out   std_logic;                                         -- clk
            phy_clk_2_clk               : out   std_logic;                                         -- clk
            phy_clk_3_clk               : out   std_logic;                                         -- clk
            wmcrst_n_2_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_3_reset_n          : out   std_logic;                                         -- reset_n
            axi_2_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_2_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_2_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_2_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_2_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_2_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_2_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_2_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_2_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_2_1_awready             : out   std_logic;                                         -- awready
            axi_2_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_2_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_2_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_2_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_2_1_wready              : out   std_logic;                                         -- wready
            axi_2_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_2_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_2_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_2_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_2_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_2_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_2_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_2_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_2_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_2_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_2_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_2_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_2_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_2_1_arready             : out   std_logic;                                         -- arready
            axi_2_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_2_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_2_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_2_1_rlast               : out   std_logic;                                         -- rlast
            axi_2_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_2_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_2_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_2_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_2_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_2_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_2_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_2_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_2_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_2_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_2_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_2_0_awready             : out   std_logic;                                         -- awready
            axi_2_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_2_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_2_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_2_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_2_0_wready              : out   std_logic;                                         -- wready
            axi_2_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_2_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_2_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_2_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_2_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_2_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_2_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_2_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_2_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_2_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_2_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_2_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_2_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_2_0_arready             : out   std_logic;                                         -- arready
            axi_2_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_2_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_2_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_2_0_rlast               : out   std_logic;                                         -- rlast
            axi_2_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_2_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_3_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_3_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_3_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_3_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_3_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_3_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_3_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_3_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_3_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_3_1_awready             : out   std_logic;                                         -- awready
            axi_3_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_3_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_3_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_3_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_3_1_wready              : out   std_logic;                                         -- wready
            axi_3_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_3_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_3_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_3_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_3_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_3_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_3_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_3_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_3_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_3_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_3_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_3_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_3_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_3_1_arready             : out   std_logic;                                         -- arready
            axi_3_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_3_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_3_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_3_1_rlast               : out   std_logic;                                         -- rlast
            axi_3_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_3_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_3_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_3_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_3_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_3_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_3_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_3_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_3_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_3_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_3_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_3_0_awready             : out   std_logic;                                         -- awready
            axi_3_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_3_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_3_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_3_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_3_0_wready              : out   std_logic;                                         -- wready
            axi_3_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_3_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_3_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_3_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_3_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_3_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_3_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_3_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_3_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_3_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_3_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_3_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_3_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_3_0_arready             : out   std_logic;                                         -- arready
            axi_3_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_3_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_3_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_3_0_rlast               : out   std_logic;                                         -- rlast
            axi_3_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_3_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_2_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_2_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_2_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_2_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_2_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_2_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_2_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_2_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_3_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_3_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_3_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_3_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_3_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_3_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_3_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_3_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_2_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_2_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_2_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_2_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_2_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_2_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_2_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_2_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_3_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_3_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_3_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_3_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_3_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_3_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_3_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_3_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_4_clk               : out   std_logic;                                         -- clk
            wmc_clk_5_clk               : out   std_logic;                                         -- clk
            phy_clk_4_clk               : out   std_logic;                                         -- clk
            phy_clk_5_clk               : out   std_logic;                                         -- clk
            wmcrst_n_4_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_5_reset_n          : out   std_logic;                                         -- reset_n
            axi_4_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_4_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_4_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_4_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_4_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_4_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_4_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_4_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_4_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_4_1_awready             : out   std_logic;                                         -- awready
            axi_4_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_4_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_4_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_4_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_4_1_wready              : out   std_logic;                                         -- wready
            axi_4_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_4_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_4_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_4_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_4_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_4_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_4_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_4_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_4_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_4_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_4_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_4_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_4_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_4_1_arready             : out   std_logic;                                         -- arready
            axi_4_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_4_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_4_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_4_1_rlast               : out   std_logic;                                         -- rlast
            axi_4_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_4_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_4_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_4_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_4_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_4_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_4_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_4_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_4_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_4_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_4_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_4_0_awready             : out   std_logic;                                         -- awready
            axi_4_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_4_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_4_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_4_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_4_0_wready              : out   std_logic;                                         -- wready
            axi_4_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_4_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_4_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_4_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_4_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_4_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_4_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_4_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_4_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_4_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_4_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_4_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_4_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_4_0_arready             : out   std_logic;                                         -- arready
            axi_4_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_4_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_4_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_4_0_rlast               : out   std_logic;                                         -- rlast
            axi_4_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_4_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_5_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_5_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_5_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_5_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_5_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_5_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_5_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_5_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_5_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_5_1_awready             : out   std_logic;                                         -- awready
            axi_5_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_5_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_5_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_5_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_5_1_wready              : out   std_logic;                                         -- wready
            axi_5_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_5_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_5_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_5_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_5_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_5_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_5_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_5_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_5_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_5_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_5_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_5_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_5_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_5_1_arready             : out   std_logic;                                         -- arready
            axi_5_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_5_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_5_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_5_1_rlast               : out   std_logic;                                         -- rlast
            axi_5_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_5_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_5_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_5_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_5_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_5_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_5_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_5_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_5_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_5_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_5_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_5_0_awready             : out   std_logic;                                         -- awready
            axi_5_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_5_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_5_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_5_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_5_0_wready              : out   std_logic;                                         -- wready
            axi_5_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_5_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_5_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_5_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_5_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_5_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_5_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_5_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_5_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_5_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_5_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_5_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_5_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_5_0_arready             : out   std_logic;                                         -- arready
            axi_5_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_5_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_5_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_5_0_rlast               : out   std_logic;                                         -- rlast
            axi_5_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_5_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_4_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_4_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_4_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_4_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_4_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_4_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_4_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_4_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_5_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_5_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_5_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_5_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_5_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_5_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_5_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_5_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_4_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_4_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_4_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_4_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_4_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_4_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_4_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_4_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_5_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_5_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_5_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_5_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_5_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_5_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_5_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_5_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_6_clk               : out   std_logic;                                         -- clk
            wmc_clk_7_clk               : out   std_logic;                                         -- clk
            phy_clk_6_clk               : out   std_logic;                                         -- clk
            phy_clk_7_clk               : out   std_logic;                                         -- clk
            wmcrst_n_6_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_7_reset_n          : out   std_logic;                                         -- reset_n
            axi_6_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_6_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_6_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_6_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_6_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_6_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_6_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_6_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_6_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_6_1_awready             : out   std_logic;                                         -- awready
            axi_6_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_6_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_6_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_6_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_6_1_wready              : out   std_logic;                                         -- wready
            axi_6_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_6_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_6_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_6_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_6_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_6_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_6_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_6_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_6_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_6_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_6_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_6_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_6_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_6_1_arready             : out   std_logic;                                         -- arready
            axi_6_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_6_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_6_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_6_1_rlast               : out   std_logic;                                         -- rlast
            axi_6_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_6_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_6_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_6_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_6_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_6_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_6_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_6_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_6_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_6_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_6_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_6_0_awready             : out   std_logic;                                         -- awready
            axi_6_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_6_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_6_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_6_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_6_0_wready              : out   std_logic;                                         -- wready
            axi_6_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_6_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_6_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_6_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_6_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_6_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_6_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_6_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_6_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_6_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_6_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_6_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_6_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_6_0_arready             : out   std_logic;                                         -- arready
            axi_6_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_6_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_6_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_6_0_rlast               : out   std_logic;                                         -- rlast
            axi_6_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_6_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_7_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_7_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_7_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_7_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_7_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_7_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_7_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_7_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_7_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_7_1_awready             : out   std_logic;                                         -- awready
            axi_7_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_7_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_7_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_7_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_7_1_wready              : out   std_logic;                                         -- wready
            axi_7_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_7_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_7_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_7_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_7_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_7_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_7_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_7_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_7_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_7_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_7_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_7_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_7_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_7_1_arready             : out   std_logic;                                         -- arready
            axi_7_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_7_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_7_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_7_1_rlast               : out   std_logic;                                         -- rlast
            axi_7_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_7_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_7_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_7_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_7_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_7_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_7_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_7_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_7_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_7_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_7_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_7_0_awready             : out   std_logic;                                         -- awready
            axi_7_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_7_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_7_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_7_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_7_0_wready              : out   std_logic;                                         -- wready
            axi_7_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_7_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_7_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_7_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_7_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_7_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_7_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_7_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_7_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_7_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_7_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_7_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_7_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_7_0_arready             : out   std_logic;                                         -- arready
            axi_7_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_7_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_7_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_7_0_rlast               : out   std_logic;                                         -- rlast
            axi_7_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_7_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_6_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_6_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_6_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_6_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_6_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_6_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_6_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_6_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_7_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_7_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_7_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_7_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_7_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_7_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_7_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_7_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_6_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_6_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_6_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_6_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_6_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_6_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_6_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_6_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_7_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_7_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_7_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_7_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_7_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_7_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_7_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_7_ur_prdata             : out   std_logic_vector(15 downto 0)                      -- ur_prdata
        );
    end component hbm_top;

    component hbm_bottom is
        port (
            pll_ref_clk                 : in    std_logic                      := 'X';             -- clk
            ext_core_clk                : in    std_logic                      := 'X';             -- clk
            ext_core_clk_locked         : in    std_logic                      := 'X';             -- export
            wmcrst_n_in                 : in    std_logic                      := 'X';             -- reset_n
            hbm_only_reset_in           : in    std_logic                      := 'X';             -- reset
            local_cal_success           : out   std_logic;                                         -- local_cal_success
            local_cal_fail              : out   std_logic;                                         -- local_cal_fail
            cal_lat                     : out   std_logic_vector(2 downto 0);                      -- cal_lat
            ck_t_0                      : out   std_logic;                                         -- ck_t
            ck_c_0                      : out   std_logic;                                         -- ck_c
            cke_0                       : out   std_logic;                                         -- cke
            c_0                         : out   std_logic_vector(7 downto 0);                      -- c
            r_0                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_0                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_0                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_0                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_0                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_0                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_0                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_0                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_0                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_0                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_0                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_0                        : out   std_logic;                                         -- rr
            rc_0                        : out   std_logic;                                         -- rc
            aerr_0                      : in    std_logic                      := 'X';             -- aerr
            ck_t_1                      : out   std_logic;                                         -- ck_t
            ck_c_1                      : out   std_logic;                                         -- ck_c
            cke_1                       : out   std_logic;                                         -- cke
            c_1                         : out   std_logic_vector(7 downto 0);                      -- c
            r_1                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_1                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_1                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_1                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_1                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_1                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_1                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_1                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_1                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_1                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_1                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_1                        : out   std_logic;                                         -- rr
            rc_1                        : out   std_logic;                                         -- rc
            aerr_1                      : in    std_logic                      := 'X';             -- aerr
            ck_t_2                      : out   std_logic;                                         -- ck_t
            ck_c_2                      : out   std_logic;                                         -- ck_c
            cke_2                       : out   std_logic;                                         -- cke
            c_2                         : out   std_logic_vector(7 downto 0);                      -- c
            r_2                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_2                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_2                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_2                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_2                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_2                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_2                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_2                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_2                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_2                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_2                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_2                        : out   std_logic;                                         -- rr
            rc_2                        : out   std_logic;                                         -- rc
            aerr_2                      : in    std_logic                      := 'X';             -- aerr
            ck_t_3                      : out   std_logic;                                         -- ck_t
            ck_c_3                      : out   std_logic;                                         -- ck_c
            cke_3                       : out   std_logic;                                         -- cke
            c_3                         : out   std_logic_vector(7 downto 0);                      -- c
            r_3                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_3                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_3                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_3                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_3                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_3                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_3                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_3                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_3                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_3                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_3                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_3                        : out   std_logic;                                         -- rr
            rc_3                        : out   std_logic;                                         -- rc
            aerr_3                      : in    std_logic                      := 'X';             -- aerr
            ck_t_4                      : out   std_logic;                                         -- ck_t
            ck_c_4                      : out   std_logic;                                         -- ck_c
            cke_4                       : out   std_logic;                                         -- cke
            c_4                         : out   std_logic_vector(7 downto 0);                      -- c
            r_4                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_4                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_4                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_4                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_4                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_4                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_4                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_4                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_4                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_4                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_4                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_4                        : out   std_logic;                                         -- rr
            rc_4                        : out   std_logic;                                         -- rc
            aerr_4                      : in    std_logic                      := 'X';             -- aerr
            ck_t_5                      : out   std_logic;                                         -- ck_t
            ck_c_5                      : out   std_logic;                                         -- ck_c
            cke_5                       : out   std_logic;                                         -- cke
            c_5                         : out   std_logic_vector(7 downto 0);                      -- c
            r_5                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_5                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_5                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_5                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_5                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_5                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_5                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_5                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_5                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_5                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_5                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_5                        : out   std_logic;                                         -- rr
            rc_5                        : out   std_logic;                                         -- rc
            aerr_5                      : in    std_logic                      := 'X';             -- aerr
            ck_t_6                      : out   std_logic;                                         -- ck_t
            ck_c_6                      : out   std_logic;                                         -- ck_c
            cke_6                       : out   std_logic;                                         -- cke
            c_6                         : out   std_logic_vector(7 downto 0);                      -- c
            r_6                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_6                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_6                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_6                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_6                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_6                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_6                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_6                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_6                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_6                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_6                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_6                        : out   std_logic;                                         -- rr
            rc_6                        : out   std_logic;                                         -- rc
            aerr_6                      : in    std_logic                      := 'X';             -- aerr
            ck_t_7                      : out   std_logic;                                         -- ck_t
            ck_c_7                      : out   std_logic;                                         -- ck_c
            cke_7                       : out   std_logic;                                         -- cke
            c_7                         : out   std_logic_vector(7 downto 0);                      -- c
            r_7                         : out   std_logic_vector(5 downto 0);                      -- r
            dq_7                        : inout std_logic_vector(127 downto 0) := (others => 'X'); -- dq
            dm_7                        : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dm
            dbi_7                       : inout std_logic_vector(15 downto 0)  := (others => 'X'); -- dbi
            par_7                       : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- par
            derr_7                      : inout std_logic_vector(3 downto 0)   := (others => 'X'); -- derr
            rdqs_t_7                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_t
            rdqs_c_7                    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- rdqs_c
            wdqs_t_7                    : out   std_logic_vector(3 downto 0);                      -- wdqs_t
            wdqs_c_7                    : out   std_logic_vector(3 downto 0);                      -- wdqs_c
            rd_7                        : inout std_logic_vector(7 downto 0)   := (others => 'X'); -- rd
            rr_7                        : out   std_logic;                                         -- rr
            rc_7                        : out   std_logic;                                         -- rc
            aerr_7                      : in    std_logic                      := 'X';             -- aerr
            cattrip                     : in    std_logic                      := 'X';             -- cattrip
            temp                        : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- temp
            wso                         : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- wso
            reset_n                     : out   std_logic;                                         -- reset_n
            wrst_n                      : out   std_logic;                                         -- wrst_n
            wrck                        : out   std_logic;                                         -- wrck
            shiftwr                     : out   std_logic;                                         -- shiftwr
            capturewr                   : out   std_logic;                                         -- capturewr
            updatewr                    : out   std_logic;                                         -- updatewr
            selectwir                   : out   std_logic;                                         -- selectwir
            wsi                         : out   std_logic;                                         -- wsi
            wmc_clk_0_clk               : out   std_logic;                                         -- clk
            wmc_clk_1_clk               : out   std_logic;                                         -- clk
            phy_clk_0_clk               : out   std_logic;                                         -- clk
            phy_clk_1_clk               : out   std_logic;                                         -- clk
            wmcrst_n_0_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_1_reset_n          : out   std_logic;                                         -- reset_n
            axi_0_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_0_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_0_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_0_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_0_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_0_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_0_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_0_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_0_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_0_0_awready             : out   std_logic;                                         -- awready
            axi_0_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_0_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_0_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_0_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_0_0_wready              : out   std_logic;                                         -- wready
            axi_0_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_0_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_0_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_0_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_0_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_0_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_0_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_0_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_0_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_0_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_0_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_0_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_0_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_0_0_arready             : out   std_logic;                                         -- arready
            axi_0_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_0_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_0_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_0_0_rlast               : out   std_logic;                                         -- rlast
            axi_0_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_0_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_0_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_0_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_0_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_0_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_0_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_0_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_0_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_0_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_0_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_0_1_awready             : out   std_logic;                                         -- awready
            axi_0_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_0_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_0_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_0_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_0_1_wready              : out   std_logic;                                         -- wready
            axi_0_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_0_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_0_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_0_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_0_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_0_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_0_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_0_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_0_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_0_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_0_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_0_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_0_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_0_1_arready             : out   std_logic;                                         -- arready
            axi_0_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_0_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_0_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_0_1_rlast               : out   std_logic;                                         -- rlast
            axi_0_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_0_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_1_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_1_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_1_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_1_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_1_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_1_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_1_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_1_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_1_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_1_0_awready             : out   std_logic;                                         -- awready
            axi_1_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_1_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_1_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_1_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_1_0_wready              : out   std_logic;                                         -- wready
            axi_1_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_1_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_1_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_1_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_1_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_1_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_1_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_1_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_1_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_1_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_1_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_1_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_1_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_1_0_arready             : out   std_logic;                                         -- arready
            axi_1_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_1_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_1_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_1_0_rlast               : out   std_logic;                                         -- rlast
            axi_1_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_1_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_1_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_1_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_1_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_1_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_1_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_1_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_1_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_1_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_1_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_1_1_awready             : out   std_logic;                                         -- awready
            axi_1_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_1_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_1_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_1_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_1_1_wready              : out   std_logic;                                         -- wready
            axi_1_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_1_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_1_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_1_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_1_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_1_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_1_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_1_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_1_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_1_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_1_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_1_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_1_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_1_1_arready             : out   std_logic;                                         -- arready
            axi_1_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_1_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_1_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_1_1_rlast               : out   std_logic;                                         -- rlast
            axi_1_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_1_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_0_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_0_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_0_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_0_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_0_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_0_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_0_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_0_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_1_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_1_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_1_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_1_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_1_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_1_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_1_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_1_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_0_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_0_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_0_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_0_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_0_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_0_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_0_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_0_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_1_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_1_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_1_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_1_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_1_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_1_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_1_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_1_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_2_clk               : out   std_logic;                                         -- clk
            wmc_clk_3_clk               : out   std_logic;                                         -- clk
            phy_clk_2_clk               : out   std_logic;                                         -- clk
            phy_clk_3_clk               : out   std_logic;                                         -- clk
            wmcrst_n_2_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_3_reset_n          : out   std_logic;                                         -- reset_n
            axi_2_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_2_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_2_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_2_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_2_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_2_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_2_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_2_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_2_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_2_0_awready             : out   std_logic;                                         -- awready
            axi_2_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_2_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_2_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_2_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_2_0_wready              : out   std_logic;                                         -- wready
            axi_2_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_2_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_2_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_2_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_2_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_2_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_2_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_2_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_2_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_2_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_2_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_2_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_2_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_2_0_arready             : out   std_logic;                                         -- arready
            axi_2_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_2_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_2_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_2_0_rlast               : out   std_logic;                                         -- rlast
            axi_2_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_2_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_2_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_2_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_2_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_2_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_2_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_2_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_2_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_2_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_2_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_2_1_awready             : out   std_logic;                                         -- awready
            axi_2_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_2_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_2_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_2_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_2_1_wready              : out   std_logic;                                         -- wready
            axi_2_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_2_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_2_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_2_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_2_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_2_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_2_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_2_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_2_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_2_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_2_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_2_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_2_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_2_1_arready             : out   std_logic;                                         -- arready
            axi_2_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_2_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_2_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_2_1_rlast               : out   std_logic;                                         -- rlast
            axi_2_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_2_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_3_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_3_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_3_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_3_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_3_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_3_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_3_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_3_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_3_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_3_0_awready             : out   std_logic;                                         -- awready
            axi_3_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_3_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_3_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_3_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_3_0_wready              : out   std_logic;                                         -- wready
            axi_3_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_3_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_3_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_3_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_3_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_3_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_3_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_3_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_3_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_3_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_3_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_3_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_3_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_3_0_arready             : out   std_logic;                                         -- arready
            axi_3_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_3_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_3_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_3_0_rlast               : out   std_logic;                                         -- rlast
            axi_3_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_3_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_3_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_3_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_3_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_3_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_3_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_3_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_3_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_3_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_3_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_3_1_awready             : out   std_logic;                                         -- awready
            axi_3_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_3_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_3_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_3_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_3_1_wready              : out   std_logic;                                         -- wready
            axi_3_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_3_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_3_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_3_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_3_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_3_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_3_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_3_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_3_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_3_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_3_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_3_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_3_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_3_1_arready             : out   std_logic;                                         -- arready
            axi_3_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_3_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_3_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_3_1_rlast               : out   std_logic;                                         -- rlast
            axi_3_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_3_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_2_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_2_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_2_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_2_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_2_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_2_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_2_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_2_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_3_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_3_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_3_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_3_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_3_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_3_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_3_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_3_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_2_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_2_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_2_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_2_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_2_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_2_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_2_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_2_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_3_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_3_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_3_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_3_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_3_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_3_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_3_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_3_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_4_clk               : out   std_logic;                                         -- clk
            wmc_clk_5_clk               : out   std_logic;                                         -- clk
            phy_clk_4_clk               : out   std_logic;                                         -- clk
            phy_clk_5_clk               : out   std_logic;                                         -- clk
            wmcrst_n_4_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_5_reset_n          : out   std_logic;                                         -- reset_n
            axi_4_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_4_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_4_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_4_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_4_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_4_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_4_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_4_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_4_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_4_0_awready             : out   std_logic;                                         -- awready
            axi_4_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_4_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_4_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_4_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_4_0_wready              : out   std_logic;                                         -- wready
            axi_4_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_4_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_4_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_4_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_4_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_4_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_4_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_4_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_4_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_4_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_4_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_4_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_4_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_4_0_arready             : out   std_logic;                                         -- arready
            axi_4_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_4_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_4_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_4_0_rlast               : out   std_logic;                                         -- rlast
            axi_4_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_4_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_4_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_4_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_4_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_4_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_4_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_4_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_4_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_4_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_4_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_4_1_awready             : out   std_logic;                                         -- awready
            axi_4_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_4_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_4_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_4_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_4_1_wready              : out   std_logic;                                         -- wready
            axi_4_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_4_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_4_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_4_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_4_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_4_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_4_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_4_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_4_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_4_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_4_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_4_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_4_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_4_1_arready             : out   std_logic;                                         -- arready
            axi_4_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_4_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_4_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_4_1_rlast               : out   std_logic;                                         -- rlast
            axi_4_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_4_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_5_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_5_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_5_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_5_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_5_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_5_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_5_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_5_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_5_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_5_0_awready             : out   std_logic;                                         -- awready
            axi_5_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_5_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_5_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_5_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_5_0_wready              : out   std_logic;                                         -- wready
            axi_5_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_5_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_5_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_5_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_5_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_5_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_5_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_5_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_5_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_5_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_5_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_5_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_5_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_5_0_arready             : out   std_logic;                                         -- arready
            axi_5_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_5_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_5_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_5_0_rlast               : out   std_logic;                                         -- rlast
            axi_5_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_5_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_5_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_5_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_5_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_5_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_5_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_5_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_5_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_5_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_5_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_5_1_awready             : out   std_logic;                                         -- awready
            axi_5_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_5_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_5_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_5_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_5_1_wready              : out   std_logic;                                         -- wready
            axi_5_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_5_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_5_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_5_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_5_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_5_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_5_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_5_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_5_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_5_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_5_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_5_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_5_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_5_1_arready             : out   std_logic;                                         -- arready
            axi_5_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_5_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_5_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_5_1_rlast               : out   std_logic;                                         -- rlast
            axi_5_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_5_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_4_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_4_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_4_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_4_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_4_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_4_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_4_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_4_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_5_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_5_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_5_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_5_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_5_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_5_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_5_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_5_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_4_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_4_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_4_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_4_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_4_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_4_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_4_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_4_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_5_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_5_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_5_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_5_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_5_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_5_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_5_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_5_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            wmc_clk_6_clk               : out   std_logic;                                         -- clk
            wmc_clk_7_clk               : out   std_logic;                                         -- clk
            phy_clk_6_clk               : out   std_logic;                                         -- clk
            phy_clk_7_clk               : out   std_logic;                                         -- clk
            wmcrst_n_6_reset_n          : out   std_logic;                                         -- reset_n
            wmcrst_n_7_reset_n          : out   std_logic;                                         -- reset_n
            axi_6_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_6_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_6_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_6_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_6_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_6_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_6_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_6_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_6_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_6_0_awready             : out   std_logic;                                         -- awready
            axi_6_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_6_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_6_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_6_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_6_0_wready              : out   std_logic;                                         -- wready
            axi_6_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_6_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_6_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_6_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_6_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_6_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_6_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_6_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_6_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_6_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_6_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_6_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_6_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_6_0_arready             : out   std_logic;                                         -- arready
            axi_6_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_6_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_6_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_6_0_rlast               : out   std_logic;                                         -- rlast
            axi_6_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_6_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_6_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_6_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_6_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_6_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_6_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_6_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_6_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_6_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_6_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_6_1_awready             : out   std_logic;                                         -- awready
            axi_6_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_6_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_6_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_6_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_6_1_wready              : out   std_logic;                                         -- wready
            axi_6_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_6_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_6_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_6_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_6_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_6_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_6_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_6_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_6_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_6_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_6_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_6_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_6_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_6_1_arready             : out   std_logic;                                         -- arready
            axi_6_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_6_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_6_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_6_1_rlast               : out   std_logic;                                         -- rlast
            axi_6_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_6_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_7_0_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_7_0_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_7_0_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_7_0_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_7_0_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_7_0_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_7_0_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_7_0_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_7_0_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_7_0_awready             : out   std_logic;                                         -- awready
            axi_7_0_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_7_0_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_7_0_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_7_0_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_7_0_wready              : out   std_logic;                                         -- wready
            axi_7_0_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_7_0_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_7_0_bvalid              : out   std_logic;                                         -- bvalid
            axi_7_0_bready              : in    std_logic                      := 'X';             -- bready
            axi_7_0_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_7_0_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_7_0_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_7_0_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_7_0_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_7_0_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_7_0_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_7_0_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_7_0_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_7_0_arready             : out   std_logic;                                         -- arready
            axi_7_0_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_7_0_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_7_0_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_7_0_rlast               : out   std_logic;                                         -- rlast
            axi_7_0_rvalid              : out   std_logic;                                         -- rvalid
            axi_7_0_rready              : in    std_logic                      := 'X';             -- rready
            axi_7_1_awid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- awid
            axi_7_1_awaddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- awaddr
            axi_7_1_awlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- awlen
            axi_7_1_awsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awsize
            axi_7_1_awburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- awburst
            axi_7_1_awprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- awprot
            axi_7_1_awqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- awqos
            axi_7_1_awuser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- awuser
            axi_7_1_awvalid             : in    std_logic                      := 'X';             -- awvalid
            axi_7_1_awready             : out   std_logic;                                         -- awready
            axi_7_1_wdata               : in    std_logic_vector(255 downto 0) := (others => 'X'); -- wdata
            axi_7_1_wstrb               : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wstrb
            axi_7_1_wlast               : in    std_logic                      := 'X';             -- wlast
            axi_7_1_wvalid              : in    std_logic                      := 'X';             -- wvalid
            axi_7_1_wready              : out   std_logic;                                         -- wready
            axi_7_1_bid                 : out   std_logic_vector(8 downto 0);                      -- bid
            axi_7_1_bresp               : out   std_logic_vector(1 downto 0);                      -- bresp
            axi_7_1_bvalid              : out   std_logic;                                         -- bvalid
            axi_7_1_bready              : in    std_logic                      := 'X';             -- bready
            axi_7_1_arid                : in    std_logic_vector(8 downto 0)   := (others => 'X'); -- arid
            axi_7_1_araddr              : in    std_logic_vector(27 downto 0)  := (others => 'X'); -- araddr
            axi_7_1_arlen               : in    std_logic_vector(7 downto 0)   := (others => 'X'); -- arlen
            axi_7_1_arsize              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arsize
            axi_7_1_arburst             : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- arburst
            axi_7_1_arprot              : in    std_logic_vector(2 downto 0)   := (others => 'X'); -- arprot
            axi_7_1_arqos               : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- arqos
            axi_7_1_aruser              : in    std_logic_vector(0 downto 0)   := (others => 'X'); -- aruser
            axi_7_1_arvalid             : in    std_logic                      := 'X';             -- arvalid
            axi_7_1_arready             : out   std_logic;                                         -- arready
            axi_7_1_rid                 : out   std_logic_vector(8 downto 0);                      -- rid
            axi_7_1_rdata               : out   std_logic_vector(255 downto 0);                    -- rdata
            axi_7_1_rresp               : out   std_logic_vector(1 downto 0);                      -- rresp
            axi_7_1_rlast               : out   std_logic;                                         -- rlast
            axi_7_1_rvalid              : out   std_logic;                                         -- rvalid
            axi_7_1_rready              : in    std_logic                      := 'X';             -- rready
            axi_extra_6_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_6_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_6_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_6_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_6_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_6_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_6_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_6_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_7_0_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_7_0_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_7_0_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_7_0_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            axi_extra_7_1_ruser_err_dbe : out   std_logic;                                         -- ruser_err_dbe
            axi_extra_7_1_ruser_data    : out   std_logic_vector(31 downto 0);                     -- ruser_data
            axi_extra_7_1_wuser_data    : in    std_logic_vector(31 downto 0)  := (others => 'X'); -- wuser_data
            axi_extra_7_1_wuser_strb    : in    std_logic_vector(3 downto 0)   := (others => 'X'); -- wuser_strb
            apb_6_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_6_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_6_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_6_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_6_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_6_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_6_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_6_ur_prdata             : out   std_logic_vector(15 downto 0);                     -- ur_prdata
            apb_7_ur_paddr              : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_paddr
            apb_7_ur_psel               : in    std_logic                      := 'X';             -- ur_psel
            apb_7_ur_penable            : in    std_logic                      := 'X';             -- ur_penable
            apb_7_ur_pwrite             : in    std_logic                      := 'X';             -- ur_pwrite
            apb_7_ur_pwdata             : in    std_logic_vector(15 downto 0)  := (others => 'X'); -- ur_pwdata
            apb_7_ur_pstrb              : in    std_logic_vector(1 downto 0)   := (others => 'X'); -- ur_pstrb
            apb_7_ur_prready            : out   std_logic;                                         -- ur_prready
            apb_7_ur_prdata             : out   std_logic_vector(15 downto 0)                      -- ur_prdata
        );
    end component hbm_bottom;

    -- DMA debug parameters
    constant PCIE_LANES      : natural := 16;
    constant PCIE_CLKS       : natural := 2;
    constant PCIE_CONS       : natural := 1;
    constant MISC_IN_WIDTH   : natural := 4;
    constant MISC_OUT_WIDTH  : natural := 4;
    constant ETH_LANES       : natural := 4;
    -- fpga_common does not support 2 region for MFB (100 Gbps) >> 2 DMA Streams are needed (2 DMA Modules)
    -- 2 Endpoints are set, but only 1 is used per DMA Module (division by 0 in rx_dma_medusa)
    constant DMA_ENDPOINTS   : natural := tsel(DMA_TYPE = 3, tsel(DMA_MODULES = 4, 4, 2), 1);
    constant STATUS_LEDS     : natural := 4; -- fake leds

    -- DDR4 + HBM
    constant DDR_PORTS       : integer := 2;
    constant MEM_ADDR_WIDTH  : natural := 28;
    constant MEM_DATA_WIDTH  : natural := 512;
    constant MEM_BURST_WIDTH : natural := 7;
    constant AMM_FREQ_KHZ    : natural := 300000;

    -- constant HBM_TOP_PORTS   : integer := tsel(HBM_PORTS >  0, tsel(HBM_PORTS < 16, HBM_PORTS, 16), 0);
    -- constant HBM_BOT_PORTS   : integer := tsel(HBM_PORTS > 16, HBM_PORTS - 16, 0);
    constant HBM_TOP_PORTS    : integer := 16;
    constant HBM_BOTTOM_PORTS : integer := 16;
    -- constant HBM_PORTS       : integer := HBM_TOP_PORTS + HBM_BOTTOM_PORTS;
    constant HBM_ADDR_WIDTH  : natural := 28;
    constant HBM_DATA_WIDTH  : natural := 256;
    constant HBM_BURST_WIDTH : natural := 2;
    constant HBM_ID_WIDTH    : natural := 9;
    constant HBM_LEN_WIDTH   : natural := 8;
    constant HBM_SIZE_WIDTH  : natural := 3;
    constant HBM_RESP_WIDTH  : natural := 2;
    constant HBM_PROT_WIDTH  : natural := 3;
    constant HBM_QOS_WIDTH   : natural := 4;
    constant HBM_USER_WIDTH  : natural := 1;

    signal eth_rx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_rx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_p               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);
    signal eth_tx_n               : std_logic_vector(ETH_PORTS*ETH_LANES-1 downto 0);

    signal eth_refclk_p           : std_logic_vector(ETH_PORTS-1 downto 0);
    signal eth_refclk_n           : std_logic_vector(ETH_PORTS-1 downto 0);

    signal ddr4_reset_n         : std_logic_vector(1 downto 0);
    signal ddr4_act_n           : std_logic_vector(1 downto 0);
    signal ddr4_par             : std_logic_vector(1 downto 0);
    signal ddr4_alert_n         : std_logic_vector(1 downto 0);

    -- External memory interfaces (clocked at MEM_CLK)
    signal mem_clk                : std_logic_vector(DDR_PORTS-1 downto 0);
    signal mem_rst_n              : std_logic_vector(DDR_PORTS-1 downto 0);

    signal mem_avmm_ready         : std_logic_vector(DDR_PORTS-1 downto 0);
    signal mem_avmm_read          : std_logic_vector(DDR_PORTS-1 downto 0);
    signal mem_avmm_write         : std_logic_vector(DDR_PORTS-1 downto 0);
    signal mem_avmm_address       : slv_array_t(DDR_PORTS-1 downto 0)(MEM_ADDR_WIDTH-1 downto 0);
    signal mem_avmm_burstcount    : slv_array_t(DDR_PORTS-1 downto 0)(MEM_BURST_WIDTH-1 downto 0);
    signal mem_avmm_writedata     : slv_array_t(DDR_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdata      : slv_array_t(DDR_PORTS-1 downto 0)(MEM_DATA_WIDTH-1 downto 0);
    signal mem_avmm_readdatavalid : std_logic_vector(DDR_PORTS-1 downto 0);

    signal emif_rst_req           : std_logic_vector(DDR_PORTS-1 downto 0);
    signal emif_rst_done          : std_logic_vector(DDR_PORTS-1 downto 0);
    signal emif_ecc_usr_int       : std_logic_vector(DDR_PORTS-1 downto 0);
    signal emif_cal_success       : std_logic_vector(DDR_PORTS-1 downto 0);
    signal emif_cal_fail          : std_logic_vector(DDR_PORTS-1 downto 0);

    -- HBM memory interfaces (clocked at HBM_CLK)
    signal hbm_clk                : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_rst_n              : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_init_done          : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_axi_awid           : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_awaddr         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_awlen          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_awsize         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_awburst        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_awprot         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0);
    signal hbm_axi_awqos          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0);
    signal hbm_axi_awuser         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0);
    signal hbm_axi_awvalid        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_awready        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wdata          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_wstrb          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH/8-1 downto 0);
    signal hbm_axi_wlast          : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_wready         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bid            : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_bresp          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_bvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_bready         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arid           : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_araddr         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ADDR_WIDTH-1 downto 0);
    signal hbm_axi_arlen          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_LEN_WIDTH-1 downto 0);
    signal hbm_axi_arsize         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_SIZE_WIDTH-1 downto 0);
    signal hbm_axi_arburst        : slv_array_t(HBM_PORTS-1 downto 0)(HBM_BURST_WIDTH-1 downto 0);
    signal hbm_axi_arprot         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_PROT_WIDTH-1 downto 0);
    signal hbm_axi_arqos          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_QOS_WIDTH-1 downto 0);
    signal hbm_axi_aruser         : slv_array_t(HBM_PORTS-1 downto 0)(HBM_USER_WIDTH-1 downto 0);
    signal hbm_axi_arvalid        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_arready        : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rid            : slv_array_t(HBM_PORTS-1 downto 0)(HBM_ID_WIDTH-1 downto 0);
    signal hbm_axi_rdata          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_DATA_WIDTH-1 downto 0);
    signal hbm_axi_rresp          : slv_array_t(HBM_PORTS-1 downto 0)(HBM_RESP_WIDTH-1 downto 0);
    signal hbm_axi_rlast          : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rvalid         : std_logic_vector(HBM_PORTS-1 downto 0);
    signal hbm_axi_rready         : std_logic_vector(HBM_PORTS-1 downto 0);

    signal hbm_cal_fail          : std_logic_vector(1 downto 0);
    signal hbm_rst_req           : std_logic_vector(1 downto 0);
    signal hbm_wmcrst_n          : std_logic_vector(1 downto 0);
    signal hbm_core_clk_locked   : std_logic_vector(1 downto 0);

    signal common_misc_out      : std_logic_vector(MISC_OUT_WIDTH-1 downto 0);

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

begin

    DDR4_CH0_RESET_N <= ddr4_reset_n (0);
    DDR4_CH0_ACT_N   <= ddr4_act_n   (0);
    DDR4_CH0_PAR     <= ddr4_par     (0);
    ddr4_alert_n(0)  <= DDR4_CH0_ALERT_N;
    DDR4_CH1_RESET_N <= ddr4_reset_n (1);
    DDR4_CH1_ACT_N   <= ddr4_act_n   (1);
    DDR4_CH1_PAR     <= ddr4_par     (1);
    ddr4_alert_n(1)  <= DDR4_CH1_ALERT_N;

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

        MEM_PORTS               => DDR_PORTS,
        MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH,
        MEM_DATA_WIDTH          => MEM_DATA_WIDTH,
        MEM_BURST_WIDTH         => MEM_BURST_WIDTH,
        AMM_FREQ_KHZ            => AMM_FREQ_KHZ,

        HBM_PORTS               => HBM_PORTS,
        HBM_ADDR_WIDTH          => HBM_ADDR_WIDTH,
        HBM_DATA_WIDTH          => HBM_DATA_WIDTH,
        HBM_BURST_WIDTH         => HBM_BURST_WIDTH,
        HBM_ID_WIDTH            => HBM_ID_WIDTH,
        HBM_LEN_WIDTH           => HBM_LEN_WIDTH,
        HBM_SIZE_WIDTH          => HBM_SIZE_WIDTH,
        HBM_RESP_WIDTH          => HBM_RESP_WIDTH,
        HBM_PROT_WIDTH          => HBM_PROT_WIDTH,
        HBM_QOS_WIDTH           => HBM_QOS_WIDTH,
        HBM_USER_WIDTH          => HBM_USER_WIDTH,

        BOARD                   => CARD_NAME,
        DEVICE                  => "STRATIX10"
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

        --ETH_LED_R(0)           => open,
        --ETH_LED_R(1)           => open,
        --ETH_LED_G(0)           => open,
        --ETH_LED_G(1)           => open,

        --QSFP_I2C_SCL(0)        => QSFP0_I2C_SCL,
        --QSFP_I2C_SCL(1)        => QSFP1_I2C_SCL,
        --QSFP_I2C_SDA(0)        => QSFP0_I2C_SDA,
        --QSFP_I2C_SDA(1)        => QSFP1_I2C_SDA,
        --QSFP_MODSEL_N(0)       => QSFP0_MODESEL_N,
        --QSFP_MODSEL_N(1)       => QSFP1_MODESEL_N,
        --QSFP_LPMODE(0)         => QSFP0_LPMODE,
        --QSFP_LPMODE(1)         => QSFP1_LPMODE,
        --QSFP_RESET_N(0)        => QSFP0_RESET_N,
        --QSFP_RESET_N(1)        => QSFP1_RESET_N,
        QSFP_MODPRS_N          => (others => '0'),
        QSFP_INT_N             => (others => '1'),

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


        HBM_CLK                => hbm_clk,
        HBM_RESET              => not hbm_rst_n,
        HBM_INIT_DONE          => hbm_init_done,

        HBM_AXI_ARADDR          => hbm_axi_araddr,
        HBM_AXI_ARBURST         => hbm_axi_arburst,
        HBM_AXI_ARID            => hbm_axi_arid,
        HBM_AXI_ARLEN           => hbm_axi_arlen,
        HBM_AXI_ARSIZE          => hbm_axi_arsize,
        HBM_AXI_ARVALID         => hbm_axi_arvalid,
        HBM_AXI_ARREADY         => hbm_axi_arready,

        HBM_AXI_RDATA           => hbm_axi_rdata,
        --HBM_AXI_RDATA_PARITY    => hbm_axi_rdata_parity, -- TODO
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
        --HBM_AXI_WDATA_PARITY    => hbm_axi_wdata_parity, -- TODO
        HBM_AXI_WLAST           => hbm_axi_wlast,
        HBM_AXI_WSTRB           => hbm_axi_wstrb,
        HBM_AXI_WVALID          => hbm_axi_wvalid,
        HBM_AXI_WREADY          => hbm_axi_wready,

        HBM_AXI_BID             => hbm_axi_bid,
        HBM_AXI_BRESP           => hbm_axi_bresp,
        HBM_AXI_BVALID          => hbm_axi_bvalid,
        HBM_AXI_BREADY          => hbm_axi_bready,

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
        MISC_OUT               => common_misc_out
    );

    -- =========================================================================
    --  DDR CONTROLLERS - EMIFs
    -- =========================================================================
    ddr4_0_enable_g : if MEM_PORTS >= 1 generate
        s10_emif_ip_ch0_i : component emif_ddr4_x64_ecc_bank0
        port map (
            local_reset_req           => emif_rst_req           (0),
            local_reset_done          => emif_rst_done          (0),
            pll_ref_clk               => DDR4_CH0_REF_CLK,
            ----pll_locked                => ,

            oct_rzqin                 => DDR4_CH0_RZQ                      ,
            mem_ck                    => DDR4_CH0_CK_P     (0 downto 0)    ,
            mem_ck_n                  => DDR4_CH0_CK_N     (0 downto 0)    ,
            mem_a                     => DDR4_CH0_A        (16 downto 0)   ,
            mem_act_n                 => ddr4_act_n        (0 downto 0)    ,
            mem_ba                    => DDR4_CH0_BA                       ,
            mem_bg                    => DDR4_CH0_BG                       ,
            mem_cke                   => DDR4_CH0_CKE      (0 downto 0)    ,
            mem_cs_n                  => DDR4_CH0_CS_N     (0 downto 0)    ,
            mem_odt                   => DDR4_CH0_ODT      (0 downto 0)    ,
            mem_reset_n               => ddr4_reset_n      (0 downto 0)    ,
            mem_par                   => ddr4_par          (0 downto 0)    ,
            mem_alert_n               => ddr4_alert_n      (0 downto 0)    ,
            mem_dqs                   => DDR4_CH0_DQS_P    (8 downto 0)    ,
            mem_dqs_n                 => DDR4_CH0_DQS_N    (8 downto 0)    ,
            mem_dq                    => DDR4_CH0_DQ                       ,
            mem_dbi_n                 => DDR4_CH0_DBI_N    (8 downto 0)    ,

            local_cal_success         => emif_cal_success       (0),
            local_cal_fail            => emif_cal_fail          (0),
            emif_usr_reset_n          => mem_rst_n              (0),
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
    else generate
        emif_rst_done(0)           <= '0';
        DDR4_CH0_CK_P(0 downto 0)  <= (others=>'X');
        DDR4_CH0_CK_N(0 downto 0)  <= (others=>'X');
        DDR4_CH0_A(16 downto 0)    <= (others=>'X');
        ddr4_act_n(0 downto 0)     <= (others=>'X');
        DDR4_CH0_BA                <= (others=>'X');
        DDR4_CH0_BG                <= (others=>'X');
        DDR4_CH0_CKE(0 downto 0)   <= (others=>'X');
        DDR4_CH0_CS_N(0 downto 0)  <= (others=>'X');
        DDR4_CH0_ODT(0 downto 0)   <= (others=>'X');
        ddr4_reset_n(0 downto 0)   <= (others=>'0');
        ddr4_par(0 downto 0)       <= (others=>'X');
        DDR4_CH0_DQS_P(8 downto 0) <= (others=>'Z');
        DDR4_CH0_DQS_N(8 downto 0) <= (others=>'Z');
        DDR4_CH0_DQ                <= (others=>'Z');
        DDR4_CH0_DBI_N(8 downto 0) <= (others=>'Z');
        emif_cal_success(0)        <= '0';
        emif_cal_fail(0)           <= '0';
        mem_rst_n(0)               <= '0';
        mem_clk(0)                 <= '0';
        emif_ecc_usr_int(0)        <= '0';
        mem_avmm_ready(0)          <= '1';
        mem_avmm_readdata(0)       <= (others=>'1');
        mem_avmm_readdatavalid (0) <= mem_avmm_read(0);
    end generate;

    ddr4_1_enable_g : if MEM_PORTS >= 2 generate
        s10_emif_ip_ch1_i : component emif_ddr4_x64_ecc_bank1
        port map (
            local_reset_req           => emif_rst_req           (1),
            local_reset_done          => emif_rst_done          (1),
            pll_ref_clk               => DDR4_CH1_REF_CLK,
            ----pll_locked                => ,

            oct_rzqin                 => DDR4_CH1_RZQ                      ,
            mem_ck                    => DDR4_CH1_CK_P     (0 downto 0)    ,
            mem_ck_n                  => DDR4_CH1_CK_N     (0 downto 0)    ,
            mem_a                     => DDR4_CH1_A        (16 downto 0)   ,
            mem_act_n                 => ddr4_act_n        (1 downto 1)    ,
            mem_ba                    => DDR4_CH1_BA                       ,
            mem_bg                    => DDR4_CH1_BG                       ,
            mem_cke                   => DDR4_CH1_CKE      (0 downto 0)    ,
            mem_cs_n                  => DDR4_CH1_CS_N     (0 downto 0)    ,
            mem_odt                   => DDR4_CH1_ODT      (0 downto 0)    ,
            mem_reset_n               => ddr4_reset_n      (1 downto 1)    ,
            mem_par                   => ddr4_par          (1 downto 1)    ,
            mem_alert_n               => ddr4_alert_n      (1 downto 1)    ,
            mem_dqs                   => DDR4_CH1_DQS_P    (8 downto 0)    ,
            mem_dqs_n                 => DDR4_CH1_DQS_N    (8 downto 0)    ,
            mem_dq                    => DDR4_CH1_DQ                       ,
            mem_dbi_n                 => DDR4_CH1_DBI_N    (8 downto 0)    ,

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
    else generate
        emif_rst_done(0)           <= '0';
        DDR4_CH1_CK_P(0 downto 0)  <= (others=>'X');
        DDR4_CH1_CK_N(0 downto 0)  <= (others=>'X');
        DDR4_CH1_A(16 downto 0)    <= (others=>'X');
        ddr4_act_n(1 downto 1)     <= (others=>'X');
        DDR4_CH1_BA                <= (others=>'X');
        DDR4_CH1_BG                <= (others=>'X');
        DDR4_CH1_CKE(0 downto 0)   <= (others=>'X');
        DDR4_CH1_CS_N(0 downto 0)  <= (others=>'X');
        DDR4_CH1_ODT(0 downto 0)   <= (others=>'X');
        ddr4_reset_n(1 downto 1)   <= (others=>'0');
        ddr4_par(1 downto 1)       <= (others=>'X');
        DDR4_CH1_DQS_P(8 downto 0) <= (others=>'Z');
        DDR4_CH1_DQS_N(8 downto 0) <= (others=>'Z');
        DDR4_CH1_DQ                <= (others=>'Z');
        DDR4_CH1_DBI_N(8 downto 0) <= (others=>'Z');
        emif_cal_success(1)        <= '0';
        emif_cal_fail(1)           <= '0';
        mem_rst_n(1)               <= '0';
        mem_clk(1)                 <= '0';
        emif_ecc_usr_int(1)        <= '0';
        mem_avmm_ready(1)          <= '1';
        mem_avmm_readdata(1)       <= (others=>'1');
        mem_avmm_readdatavalid (1) <= mem_avmm_read(1);
    end generate;

    -- =========================================================================
    --  HBM CONTROLLERS
    -- =========================================================================

    -- HBM reset
    hbm_rst_req <= (others => '0'); -- not rst request
    hbm_wmcrst_n <= not hbm_rst_req;
    hbm_core_clk_locked <= (others => (not common_misc_out(3)));

    -- HBM TOP
    hbm_top_g: if HBM_PORTS > 0 generate
        hbm_top_i : component hbm_top
        port map (
            pll_ref_clk                                       => HBM_TOP_REF_CLK,
            ext_core_clk                                      => common_misc_out(2),
            ext_core_clk_locked                               => hbm_core_clk_locked(0),
            wmcrst_n_in                                       => hbm_wmcrst_n(0),
            hbm_only_reset_in                                 => hbm_rst_req(0),
            local_cal_success                                 => hbm_init_done(0),
            local_cal_fail                                    => hbm_cal_fail(0),
            cattrip                                           => HBM_TOP_CATTRIP,
            temp                                              => HBM_TOP_TEMP,
            wso                                               => HBM_TOP_WSO,
            reset_n                                           => HBM_TOP_RESET_N,
            wrst_n                                            => HBM_TOP_WRST_N,
            wrck                                              => HBM_TOP_WRCK,
            shiftwr                                           => HBM_TOP_SHIFTWR,
            capturewr                                         => HBM_TOP_CAPTUREWR,
            updatewr                                          => HBM_TOP_UPDATEWR,
            selectwir                                         => HBM_TOP_SELECTWIR,
            wsi                                               => HBM_TOP_WSI,

            wmc_clk_0_clk                                     => hbm_clk(0),
            wmc_clk_1_clk                                     => hbm_clk(2),
            wmcrst_n_0_reset_n                                => hbm_rst_n(0),
            wmcrst_n_1_reset_n                                => hbm_rst_n(2),

            axi_0_1_awid                                      => hbm_axi_awid(1),
            axi_0_1_awaddr                                    => hbm_axi_awaddr(1),
            axi_0_1_awlen                                     => hbm_axi_awlen(1),
            axi_0_1_awsize                                    => hbm_axi_awsize(1),
            axi_0_1_awburst                                   => hbm_axi_awburst(1),
            axi_0_1_awprot                                    => hbm_axi_awprot(1),
            axi_0_1_awqos                                     => hbm_axi_awqos(1),
            axi_0_1_awuser                                    => hbm_axi_awuser(1),
            axi_0_1_awvalid                                   => hbm_axi_awvalid(1),
            axi_0_1_awready                                   => hbm_axi_awready(1),
            axi_0_1_wdata                                     => hbm_axi_wdata(1),
            axi_0_1_wstrb                                     => hbm_axi_wstrb(1),
            axi_0_1_wlast                                     => hbm_axi_wlast(1),
            axi_0_1_wvalid                                    => hbm_axi_wvalid(1),
            axi_0_1_wready                                    => hbm_axi_wready(1),
            axi_0_1_bid                                       => hbm_axi_bid(1),
            axi_0_1_bresp                                     => hbm_axi_bresp(1),
            axi_0_1_bvalid                                    => hbm_axi_bvalid(1),
            axi_0_1_bready                                    => hbm_axi_bready(1),
            axi_0_1_arid                                      => hbm_axi_arid(1),
            axi_0_1_araddr                                    => hbm_axi_araddr(1),
            axi_0_1_arlen                                     => hbm_axi_arlen(1),
            axi_0_1_arsize                                    => hbm_axi_arsize(1),
            axi_0_1_arburst                                   => hbm_axi_arburst(1),
            axi_0_1_arprot                                    => hbm_axi_arprot(1),
            axi_0_1_arqos                                     => hbm_axi_arqos(1),
            axi_0_1_aruser                                    => hbm_axi_aruser(1),
            axi_0_1_arvalid                                   => hbm_axi_arvalid(1),
            axi_0_1_arready                                   => hbm_axi_arready(1),
            axi_0_1_rid                                       => hbm_axi_rid(1),
            axi_0_1_rdata                                     => hbm_axi_rdata(1),
            axi_0_1_rresp                                     => hbm_axi_rresp(1),
            axi_0_1_rlast                                     => hbm_axi_rlast(1),
            axi_0_1_rvalid                                    => hbm_axi_rvalid(1),
            axi_0_1_rready                                    => hbm_axi_rready(1),

            axi_0_0_awid                                      => hbm_axi_awid(0),
            axi_0_0_awaddr                                    => hbm_axi_awaddr(0),
            axi_0_0_awlen                                     => hbm_axi_awlen(0),
            axi_0_0_awsize                                    => hbm_axi_awsize(0),
            axi_0_0_awburst                                   => hbm_axi_awburst(0),
            axi_0_0_awprot                                    => hbm_axi_awprot(0),
            axi_0_0_awqos                                     => hbm_axi_awqos(0),
            axi_0_0_awuser                                    => hbm_axi_awuser(0),
            axi_0_0_awvalid                                   => hbm_axi_awvalid(0),
            axi_0_0_awready                                   => hbm_axi_awready(0),
            axi_0_0_wdata                                     => hbm_axi_wdata(0),
            axi_0_0_wstrb                                     => hbm_axi_wstrb(0),
            axi_0_0_wlast                                     => hbm_axi_wlast(0),
            axi_0_0_wvalid                                    => hbm_axi_wvalid(0),
            axi_0_0_wready                                    => hbm_axi_wready(0),
            axi_0_0_bid                                       => hbm_axi_bid(0),
            axi_0_0_bresp                                     => hbm_axi_bresp(0),
            axi_0_0_bvalid                                    => hbm_axi_bvalid(0),
            axi_0_0_bready                                    => hbm_axi_bready(0),
            axi_0_0_arid                                      => hbm_axi_arid(0),
            axi_0_0_araddr                                    => hbm_axi_araddr(0),
            axi_0_0_arlen                                     => hbm_axi_arlen(0),
            axi_0_0_arsize                                    => hbm_axi_arsize(0),
            axi_0_0_arburst                                   => hbm_axi_arburst(0),
            axi_0_0_arprot                                    => hbm_axi_arprot(0),
            axi_0_0_arqos                                     => hbm_axi_arqos(0),
            axi_0_0_aruser                                    => hbm_axi_aruser(0),
            axi_0_0_arvalid                                   => hbm_axi_arvalid(0),
            axi_0_0_arready                                   => hbm_axi_arready(0),
            axi_0_0_rid                                       => hbm_axi_rid(0),
            axi_0_0_rdata                                     => hbm_axi_rdata(0),
            axi_0_0_rresp                                     => hbm_axi_rresp(0),
            axi_0_0_rlast                                     => hbm_axi_rlast(0),
            axi_0_0_rvalid                                    => hbm_axi_rvalid(0),
            axi_0_0_rready                                    => hbm_axi_rready(0),

            axi_1_1_awid                                      => hbm_axi_awid(3),
            axi_1_1_awaddr                                    => hbm_axi_awaddr(3),
            axi_1_1_awlen                                     => hbm_axi_awlen(3),
            axi_1_1_awsize                                    => hbm_axi_awsize(3),
            axi_1_1_awburst                                   => hbm_axi_awburst(3),
            axi_1_1_awprot                                    => hbm_axi_awprot(3),
            axi_1_1_awqos                                     => hbm_axi_awqos(3),
            axi_1_1_awuser                                    => hbm_axi_awuser(3),
            axi_1_1_awvalid                                   => hbm_axi_awvalid(3),
            axi_1_1_awready                                   => hbm_axi_awready(3),
            axi_1_1_wdata                                     => hbm_axi_wdata(3),
            axi_1_1_wstrb                                     => hbm_axi_wstrb(3),
            axi_1_1_wlast                                     => hbm_axi_wlast(3),
            axi_1_1_wvalid                                    => hbm_axi_wvalid(3),
            axi_1_1_wready                                    => hbm_axi_wready(3),
            axi_1_1_bid                                       => hbm_axi_bid(3),
            axi_1_1_bresp                                     => hbm_axi_bresp(3),
            axi_1_1_bvalid                                    => hbm_axi_bvalid(3),
            axi_1_1_bready                                    => hbm_axi_bready(3),
            axi_1_1_arid                                      => hbm_axi_arid(3),
            axi_1_1_araddr                                    => hbm_axi_araddr(3),
            axi_1_1_arlen                                     => hbm_axi_arlen(3),
            axi_1_1_arsize                                    => hbm_axi_arsize(3),
            axi_1_1_arburst                                   => hbm_axi_arburst(3),
            axi_1_1_arprot                                    => hbm_axi_arprot(3),
            axi_1_1_arqos                                     => hbm_axi_arqos(3),
            axi_1_1_aruser                                    => hbm_axi_aruser(3),
            axi_1_1_arvalid                                   => hbm_axi_arvalid(3),
            axi_1_1_arready                                   => hbm_axi_arready(3),
            axi_1_1_rid                                       => hbm_axi_rid(3),
            axi_1_1_rdata                                     => hbm_axi_rdata(3),
            axi_1_1_rresp                                     => hbm_axi_rresp(3),
            axi_1_1_rlast                                     => hbm_axi_rlast(3),
            axi_1_1_rvalid                                    => hbm_axi_rvalid(3),
            axi_1_1_rready                                    => hbm_axi_rready(3),

            axi_1_0_awid                                      => hbm_axi_awid(2),
            axi_1_0_awaddr                                    => hbm_axi_awaddr(2),
            axi_1_0_awlen                                     => hbm_axi_awlen(2),
            axi_1_0_awsize                                    => hbm_axi_awsize(2),
            axi_1_0_awburst                                   => hbm_axi_awburst(2),
            axi_1_0_awprot                                    => hbm_axi_awprot(2),
            axi_1_0_awqos                                     => hbm_axi_awqos(2),
            axi_1_0_awuser                                    => hbm_axi_awuser(2),
            axi_1_0_awvalid                                   => hbm_axi_awvalid(2),
            axi_1_0_awready                                   => hbm_axi_awready(2),
            axi_1_0_wdata                                     => hbm_axi_wdata(2),
            axi_1_0_wstrb                                     => hbm_axi_wstrb(2),
            axi_1_0_wlast                                     => hbm_axi_wlast(2),
            axi_1_0_wvalid                                    => hbm_axi_wvalid(2),
            axi_1_0_wready                                    => hbm_axi_wready(2),
            axi_1_0_bid                                       => hbm_axi_bid(2),
            axi_1_0_bresp                                     => hbm_axi_bresp(2),
            axi_1_0_bvalid                                    => hbm_axi_bvalid(2),
            axi_1_0_bready                                    => hbm_axi_bready(2),
            axi_1_0_arid                                      => hbm_axi_arid(2),
            axi_1_0_araddr                                    => hbm_axi_araddr(2),
            axi_1_0_arlen                                     => hbm_axi_arlen(2),
            axi_1_0_arsize                                    => hbm_axi_arsize(2),
            axi_1_0_arburst                                   => hbm_axi_arburst(2),
            axi_1_0_arprot                                    => hbm_axi_arprot(2),
            axi_1_0_arqos                                     => hbm_axi_arqos(2),
            axi_1_0_aruser                                    => hbm_axi_aruser(2),
            axi_1_0_arvalid                                   => hbm_axi_arvalid(2),
            axi_1_0_arready                                   => hbm_axi_arready(2),
            axi_1_0_rid                                       => hbm_axi_rid(2),
            axi_1_0_rdata                                     => hbm_axi_rdata(2),
            axi_1_0_rresp                                     => hbm_axi_rresp(2),
            axi_1_0_rlast                                     => hbm_axi_rlast(2),
            axi_1_0_rvalid                                    => hbm_axi_rvalid(2),
            axi_1_0_rready                                    => hbm_axi_rready(2),

            wmc_clk_2_clk                                     => hbm_clk(4),
            wmc_clk_3_clk                                     => hbm_clk(6),
            wmcrst_n_2_reset_n                                => hbm_rst_n(4),
            wmcrst_n_3_reset_n                                => hbm_rst_n(6),

            axi_2_1_awid                                      => hbm_axi_awid(5),
            axi_2_1_awaddr                                    => hbm_axi_awaddr(5),
            axi_2_1_awlen                                     => hbm_axi_awlen(5),
            axi_2_1_awsize                                    => hbm_axi_awsize(5),
            axi_2_1_awburst                                   => hbm_axi_awburst(5),
            axi_2_1_awprot                                    => hbm_axi_awprot(5),
            axi_2_1_awqos                                     => hbm_axi_awqos(5),
            axi_2_1_awuser                                    => hbm_axi_awuser(5),
            axi_2_1_awvalid                                   => hbm_axi_awvalid(5),
            axi_2_1_awready                                   => hbm_axi_awready(5),
            axi_2_1_wdata                                     => hbm_axi_wdata(5),
            axi_2_1_wstrb                                     => hbm_axi_wstrb(5),
            axi_2_1_wlast                                     => hbm_axi_wlast(5),
            axi_2_1_wvalid                                    => hbm_axi_wvalid(5),
            axi_2_1_wready                                    => hbm_axi_wready(5),
            axi_2_1_bid                                       => hbm_axi_bid(5),
            axi_2_1_bresp                                     => hbm_axi_bresp(5),
            axi_2_1_bvalid                                    => hbm_axi_bvalid(5),
            axi_2_1_bready                                    => hbm_axi_bready(5),
            axi_2_1_arid                                      => hbm_axi_arid(5),
            axi_2_1_araddr                                    => hbm_axi_araddr(5),
            axi_2_1_arlen                                     => hbm_axi_arlen(5),
            axi_2_1_arsize                                    => hbm_axi_arsize(5),
            axi_2_1_arburst                                   => hbm_axi_arburst(5),
            axi_2_1_arprot                                    => hbm_axi_arprot(5),
            axi_2_1_arqos                                     => hbm_axi_arqos(5),
            axi_2_1_aruser                                    => hbm_axi_aruser(5),
            axi_2_1_arvalid                                   => hbm_axi_arvalid(5),
            axi_2_1_arready                                   => hbm_axi_arready(5),
            axi_2_1_rid                                       => hbm_axi_rid(5),
            axi_2_1_rdata                                     => hbm_axi_rdata(5),
            axi_2_1_rresp                                     => hbm_axi_rresp(5),
            axi_2_1_rlast                                     => hbm_axi_rlast(5),
            axi_2_1_rvalid                                    => hbm_axi_rvalid(5),
            axi_2_1_rready                                    => hbm_axi_rready(5),

            axi_2_0_awid                                      => hbm_axi_awid(4),
            axi_2_0_awaddr                                    => hbm_axi_awaddr(4),
            axi_2_0_awlen                                     => hbm_axi_awlen(4),
            axi_2_0_awsize                                    => hbm_axi_awsize(4),
            axi_2_0_awburst                                   => hbm_axi_awburst(4),
            axi_2_0_awprot                                    => hbm_axi_awprot(4),
            axi_2_0_awqos                                     => hbm_axi_awqos(4),
            axi_2_0_awuser                                    => hbm_axi_awuser(4),
            axi_2_0_awvalid                                   => hbm_axi_awvalid(4),
            axi_2_0_awready                                   => hbm_axi_awready(4),
            axi_2_0_wdata                                     => hbm_axi_wdata(4),
            axi_2_0_wstrb                                     => hbm_axi_wstrb(4),
            axi_2_0_wlast                                     => hbm_axi_wlast(4),
            axi_2_0_wvalid                                    => hbm_axi_wvalid(4),
            axi_2_0_wready                                    => hbm_axi_wready(4),
            axi_2_0_bid                                       => hbm_axi_bid(4),
            axi_2_0_bresp                                     => hbm_axi_bresp(4),
            axi_2_0_bvalid                                    => hbm_axi_bvalid(4),
            axi_2_0_bready                                    => hbm_axi_bready(4),
            axi_2_0_arid                                      => hbm_axi_arid(4),
            axi_2_0_araddr                                    => hbm_axi_araddr(4),
            axi_2_0_arlen                                     => hbm_axi_arlen(4),
            axi_2_0_arsize                                    => hbm_axi_arsize(4),
            axi_2_0_arburst                                   => hbm_axi_arburst(4),
            axi_2_0_arprot                                    => hbm_axi_arprot(4),
            axi_2_0_arqos                                     => hbm_axi_arqos(4),
            axi_2_0_aruser                                    => hbm_axi_aruser(4),
            axi_2_0_arvalid                                   => hbm_axi_arvalid(4),
            axi_2_0_arready                                   => hbm_axi_arready(4),
            axi_2_0_rid                                       => hbm_axi_rid(4),
            axi_2_0_rdata                                     => hbm_axi_rdata(4),
            axi_2_0_rresp                                     => hbm_axi_rresp(4),
            axi_2_0_rlast                                     => hbm_axi_rlast(4),
            axi_2_0_rvalid                                    => hbm_axi_rvalid(4),
            axi_2_0_rready                                    => hbm_axi_rready(4),

            axi_3_1_awid                                      => hbm_axi_awid(7),
            axi_3_1_awaddr                                    => hbm_axi_awaddr(7),
            axi_3_1_awlen                                     => hbm_axi_awlen(7),
            axi_3_1_awsize                                    => hbm_axi_awsize(7),
            axi_3_1_awburst                                   => hbm_axi_awburst(7),
            axi_3_1_awprot                                    => hbm_axi_awprot(7),
            axi_3_1_awqos                                     => hbm_axi_awqos(7),
            axi_3_1_awuser                                    => hbm_axi_awuser(7),
            axi_3_1_awvalid                                   => hbm_axi_awvalid(7),
            axi_3_1_awready                                   => hbm_axi_awready(7),
            axi_3_1_wdata                                     => hbm_axi_wdata(7),
            axi_3_1_wstrb                                     => hbm_axi_wstrb(7),
            axi_3_1_wlast                                     => hbm_axi_wlast(7),
            axi_3_1_wvalid                                    => hbm_axi_wvalid(7),
            axi_3_1_wready                                    => hbm_axi_wready(7),
            axi_3_1_bid                                       => hbm_axi_bid(7),
            axi_3_1_bresp                                     => hbm_axi_bresp(7),
            axi_3_1_bvalid                                    => hbm_axi_bvalid(7),
            axi_3_1_bready                                    => hbm_axi_bready(7),
            axi_3_1_arid                                      => hbm_axi_arid(7),
            axi_3_1_araddr                                    => hbm_axi_araddr(7),
            axi_3_1_arlen                                     => hbm_axi_arlen(7),
            axi_3_1_arsize                                    => hbm_axi_arsize(7),
            axi_3_1_arburst                                   => hbm_axi_arburst(7),
            axi_3_1_arprot                                    => hbm_axi_arprot(7),
            axi_3_1_arqos                                     => hbm_axi_arqos(7),
            axi_3_1_aruser                                    => hbm_axi_aruser(7),
            axi_3_1_arvalid                                   => hbm_axi_arvalid(7),
            axi_3_1_arready                                   => hbm_axi_arready(7),
            axi_3_1_rid                                       => hbm_axi_rid(7),
            axi_3_1_rdata                                     => hbm_axi_rdata(7),
            axi_3_1_rresp                                     => hbm_axi_rresp(7),
            axi_3_1_rlast                                     => hbm_axi_rlast(7),
            axi_3_1_rvalid                                    => hbm_axi_rvalid(7),
            axi_3_1_rready                                    => hbm_axi_rready(7),

            axi_3_0_awid                                      => hbm_axi_awid(6),
            axi_3_0_awaddr                                    => hbm_axi_awaddr(6),
            axi_3_0_awlen                                     => hbm_axi_awlen(6),
            axi_3_0_awsize                                    => hbm_axi_awsize(6),
            axi_3_0_awburst                                   => hbm_axi_awburst(6),
            axi_3_0_awprot                                    => hbm_axi_awprot(6),
            axi_3_0_awqos                                     => hbm_axi_awqos(6),
            axi_3_0_awuser                                    => hbm_axi_awuser(6),
            axi_3_0_awvalid                                   => hbm_axi_awvalid(6),
            axi_3_0_awready                                   => hbm_axi_awready(6),
            axi_3_0_wdata                                     => hbm_axi_wdata(6),
            axi_3_0_wstrb                                     => hbm_axi_wstrb(6),
            axi_3_0_wlast                                     => hbm_axi_wlast(6),
            axi_3_0_wvalid                                    => hbm_axi_wvalid(6),
            axi_3_0_wready                                    => hbm_axi_wready(6),
            axi_3_0_bid                                       => hbm_axi_bid(6),
            axi_3_0_bresp                                     => hbm_axi_bresp(6),
            axi_3_0_bvalid                                    => hbm_axi_bvalid(6),
            axi_3_0_bready                                    => hbm_axi_bready(6),
            axi_3_0_arid                                      => hbm_axi_arid(6),
            axi_3_0_araddr                                    => hbm_axi_araddr(6),
            axi_3_0_arlen                                     => hbm_axi_arlen(6),
            axi_3_0_arsize                                    => hbm_axi_arsize(6),
            axi_3_0_arburst                                   => hbm_axi_arburst(6),
            axi_3_0_arprot                                    => hbm_axi_arprot(6),
            axi_3_0_arqos                                     => hbm_axi_arqos(6),
            axi_3_0_aruser                                    => hbm_axi_aruser(6),
            axi_3_0_arvalid                                   => hbm_axi_arvalid(6),
            axi_3_0_arready                                   => hbm_axi_arready(6),
            axi_3_0_rid                                       => hbm_axi_rid(6),
            axi_3_0_rdata                                     => hbm_axi_rdata(6),
            axi_3_0_rresp                                     => hbm_axi_rresp(6),
            axi_3_0_rlast                                     => hbm_axi_rlast(6),
            axi_3_0_rvalid                                    => hbm_axi_rvalid(6),
            axi_3_0_rready                                    => hbm_axi_rready(6),

            wmc_clk_4_clk                                     => hbm_clk(8),
            wmc_clk_5_clk                                     => hbm_clk(10),
            wmcrst_n_4_reset_n                                => hbm_rst_n(8),
            wmcrst_n_5_reset_n                                => hbm_rst_n(10),

            axi_4_1_awid                                      => hbm_axi_awid(9),
            axi_4_1_awaddr                                    => hbm_axi_awaddr(9),
            axi_4_1_awlen                                     => hbm_axi_awlen(9),
            axi_4_1_awsize                                    => hbm_axi_awsize(9),
            axi_4_1_awburst                                   => hbm_axi_awburst(9),
            axi_4_1_awprot                                    => hbm_axi_awprot(9),
            axi_4_1_awqos                                     => hbm_axi_awqos(9),
            axi_4_1_awuser                                    => hbm_axi_awuser(9),
            axi_4_1_awvalid                                   => hbm_axi_awvalid(9),
            axi_4_1_awready                                   => hbm_axi_awready(9),
            axi_4_1_wdata                                     => hbm_axi_wdata(9),
            axi_4_1_wstrb                                     => hbm_axi_wstrb(9),
            axi_4_1_wlast                                     => hbm_axi_wlast(9),
            axi_4_1_wvalid                                    => hbm_axi_wvalid(9),
            axi_4_1_wready                                    => hbm_axi_wready(9),
            axi_4_1_bid                                       => hbm_axi_bid(9),
            axi_4_1_bresp                                     => hbm_axi_bresp(9),
            axi_4_1_bvalid                                    => hbm_axi_bvalid(9),
            axi_4_1_bready                                    => hbm_axi_bready(9),
            axi_4_1_arid                                      => hbm_axi_arid(9),
            axi_4_1_araddr                                    => hbm_axi_araddr(9),
            axi_4_1_arlen                                     => hbm_axi_arlen(9),
            axi_4_1_arsize                                    => hbm_axi_arsize(9),
            axi_4_1_arburst                                   => hbm_axi_arburst(9),
            axi_4_1_arprot                                    => hbm_axi_arprot(9),
            axi_4_1_arqos                                     => hbm_axi_arqos(9),
            axi_4_1_aruser                                    => hbm_axi_aruser(9),
            axi_4_1_arvalid                                   => hbm_axi_arvalid(9),
            axi_4_1_arready                                   => hbm_axi_arready(9),
            axi_4_1_rid                                       => hbm_axi_rid(9),
            axi_4_1_rdata                                     => hbm_axi_rdata(9),
            axi_4_1_rresp                                     => hbm_axi_rresp(9),
            axi_4_1_rlast                                     => hbm_axi_rlast(9),
            axi_4_1_rvalid                                    => hbm_axi_rvalid(9),
            axi_4_1_rready                                    => hbm_axi_rready(9),

            axi_4_0_awid                                      => hbm_axi_awid(8),
            axi_4_0_awaddr                                    => hbm_axi_awaddr(8),
            axi_4_0_awlen                                     => hbm_axi_awlen(8),
            axi_4_0_awsize                                    => hbm_axi_awsize(8),
            axi_4_0_awburst                                   => hbm_axi_awburst(8),
            axi_4_0_awprot                                    => hbm_axi_awprot(8),
            axi_4_0_awqos                                     => hbm_axi_awqos(8),
            axi_4_0_awuser                                    => hbm_axi_awuser(8),
            axi_4_0_awvalid                                   => hbm_axi_awvalid(8),
            axi_4_0_awready                                   => hbm_axi_awready(8),
            axi_4_0_wdata                                     => hbm_axi_wdata(8),
            axi_4_0_wstrb                                     => hbm_axi_wstrb(8),
            axi_4_0_wlast                                     => hbm_axi_wlast(8),
            axi_4_0_wvalid                                    => hbm_axi_wvalid(8),
            axi_4_0_wready                                    => hbm_axi_wready(8),
            axi_4_0_bid                                       => hbm_axi_bid(8),
            axi_4_0_bresp                                     => hbm_axi_bresp(8),
            axi_4_0_bvalid                                    => hbm_axi_bvalid(8),
            axi_4_0_bready                                    => hbm_axi_bready(8),
            axi_4_0_arid                                      => hbm_axi_arid(8),
            axi_4_0_araddr                                    => hbm_axi_araddr(8),
            axi_4_0_arlen                                     => hbm_axi_arlen(8),
            axi_4_0_arsize                                    => hbm_axi_arsize(8),
            axi_4_0_arburst                                   => hbm_axi_arburst(8),
            axi_4_0_arprot                                    => hbm_axi_arprot(8),
            axi_4_0_arqos                                     => hbm_axi_arqos(8),
            axi_4_0_aruser                                    => hbm_axi_aruser(8),
            axi_4_0_arvalid                                   => hbm_axi_arvalid(8),
            axi_4_0_arready                                   => hbm_axi_arready(8),
            axi_4_0_rid                                       => hbm_axi_rid(8),
            axi_4_0_rdata                                     => hbm_axi_rdata(8),
            axi_4_0_rresp                                     => hbm_axi_rresp(8),
            axi_4_0_rlast                                     => hbm_axi_rlast(8),
            axi_4_0_rvalid                                    => hbm_axi_rvalid(8),
            axi_4_0_rready                                    => hbm_axi_rready(8),

            axi_5_1_awid                                      => hbm_axi_awid(11),
            axi_5_1_awaddr                                    => hbm_axi_awaddr(11),
            axi_5_1_awlen                                     => hbm_axi_awlen(11),
            axi_5_1_awsize                                    => hbm_axi_awsize(11),
            axi_5_1_awburst                                   => hbm_axi_awburst(11),
            axi_5_1_awprot                                    => hbm_axi_awprot(11),
            axi_5_1_awqos                                     => hbm_axi_awqos(11),
            axi_5_1_awuser                                    => hbm_axi_awuser(11),
            axi_5_1_awvalid                                   => hbm_axi_awvalid(11),
            axi_5_1_awready                                   => hbm_axi_awready(11),
            axi_5_1_wdata                                     => hbm_axi_wdata(11),
            axi_5_1_wstrb                                     => hbm_axi_wstrb(11),
            axi_5_1_wlast                                     => hbm_axi_wlast(11),
            axi_5_1_wvalid                                    => hbm_axi_wvalid(11),
            axi_5_1_wready                                    => hbm_axi_wready(11),
            axi_5_1_bid                                       => hbm_axi_bid(11),
            axi_5_1_bresp                                     => hbm_axi_bresp(11),
            axi_5_1_bvalid                                    => hbm_axi_bvalid(11),
            axi_5_1_bready                                    => hbm_axi_bready(11),
            axi_5_1_arid                                      => hbm_axi_arid(11),
            axi_5_1_araddr                                    => hbm_axi_araddr(11),
            axi_5_1_arlen                                     => hbm_axi_arlen(11),
            axi_5_1_arsize                                    => hbm_axi_arsize(11),
            axi_5_1_arburst                                   => hbm_axi_arburst(11),
            axi_5_1_arprot                                    => hbm_axi_arprot(11),
            axi_5_1_arqos                                     => hbm_axi_arqos(11),
            axi_5_1_aruser                                    => hbm_axi_aruser(11),
            axi_5_1_arvalid                                   => hbm_axi_arvalid(11),
            axi_5_1_arready                                   => hbm_axi_arready(11),
            axi_5_1_rid                                       => hbm_axi_rid(11),
            axi_5_1_rdata                                     => hbm_axi_rdata(11),
            axi_5_1_rresp                                     => hbm_axi_rresp(11),
            axi_5_1_rlast                                     => hbm_axi_rlast(11),
            axi_5_1_rvalid                                    => hbm_axi_rvalid(11),
            axi_5_1_rready                                    => hbm_axi_rready(11),

            axi_5_0_awid                                      => hbm_axi_awid(10),
            axi_5_0_awaddr                                    => hbm_axi_awaddr(10),
            axi_5_0_awlen                                     => hbm_axi_awlen(10),
            axi_5_0_awsize                                    => hbm_axi_awsize(10),
            axi_5_0_awburst                                   => hbm_axi_awburst(10),
            axi_5_0_awprot                                    => hbm_axi_awprot(10),
            axi_5_0_awqos                                     => hbm_axi_awqos(10),
            axi_5_0_awuser                                    => hbm_axi_awuser(10),
            axi_5_0_awvalid                                   => hbm_axi_awvalid(10),
            axi_5_0_awready                                   => hbm_axi_awready(10),
            axi_5_0_wdata                                     => hbm_axi_wdata(10),
            axi_5_0_wstrb                                     => hbm_axi_wstrb(10),
            axi_5_0_wlast                                     => hbm_axi_wlast(10),
            axi_5_0_wvalid                                    => hbm_axi_wvalid(10),
            axi_5_0_wready                                    => hbm_axi_wready(10),
            axi_5_0_bid                                       => hbm_axi_bid(10),
            axi_5_0_bresp                                     => hbm_axi_bresp(10),
            axi_5_0_bvalid                                    => hbm_axi_bvalid(10),
            axi_5_0_bready                                    => hbm_axi_bready(10),
            axi_5_0_arid                                      => hbm_axi_arid(10),
            axi_5_0_araddr                                    => hbm_axi_araddr(10),
            axi_5_0_arlen                                     => hbm_axi_arlen(10),
            axi_5_0_arsize                                    => hbm_axi_arsize(10),
            axi_5_0_arburst                                   => hbm_axi_arburst(10),
            axi_5_0_arprot                                    => hbm_axi_arprot(10),
            axi_5_0_arqos                                     => hbm_axi_arqos(10),
            axi_5_0_aruser                                    => hbm_axi_aruser(10),
            axi_5_0_arvalid                                   => hbm_axi_arvalid(10),
            axi_5_0_arready                                   => hbm_axi_arready(10),
            axi_5_0_rid                                       => hbm_axi_rid(10),
            axi_5_0_rdata                                     => hbm_axi_rdata(10),
            axi_5_0_rresp                                     => hbm_axi_rresp(10),
            axi_5_0_rlast                                     => hbm_axi_rlast(10),
            axi_5_0_rvalid                                    => hbm_axi_rvalid(10),
            axi_5_0_rready                                    => hbm_axi_rready(10),

            wmc_clk_6_clk                                     => hbm_clk(12),
            wmc_clk_7_clk                                     => hbm_clk(14),
            wmcrst_n_6_reset_n                                => hbm_rst_n(12),
            wmcrst_n_7_reset_n                                => hbm_rst_n(14),

            axi_6_1_awid                                      => hbm_axi_awid(13),
            axi_6_1_awaddr                                    => hbm_axi_awaddr(13),
            axi_6_1_awlen                                     => hbm_axi_awlen(13),
            axi_6_1_awsize                                    => hbm_axi_awsize(13),
            axi_6_1_awburst                                   => hbm_axi_awburst(13),
            axi_6_1_awprot                                    => hbm_axi_awprot(13),
            axi_6_1_awqos                                     => hbm_axi_awqos(13),
            axi_6_1_awuser                                    => hbm_axi_awuser(13),
            axi_6_1_awvalid                                   => hbm_axi_awvalid(13),
            axi_6_1_awready                                   => hbm_axi_awready(13),
            axi_6_1_wdata                                     => hbm_axi_wdata(13),
            axi_6_1_wstrb                                     => hbm_axi_wstrb(13),
            axi_6_1_wlast                                     => hbm_axi_wlast(13),
            axi_6_1_wvalid                                    => hbm_axi_wvalid(13),
            axi_6_1_wready                                    => hbm_axi_wready(13),
            axi_6_1_bid                                       => hbm_axi_bid(13),
            axi_6_1_bresp                                     => hbm_axi_bresp(13),
            axi_6_1_bvalid                                    => hbm_axi_bvalid(13),
            axi_6_1_bready                                    => hbm_axi_bready(13),
            axi_6_1_arid                                      => hbm_axi_arid(13),
            axi_6_1_araddr                                    => hbm_axi_araddr(13),
            axi_6_1_arlen                                     => hbm_axi_arlen(13),
            axi_6_1_arsize                                    => hbm_axi_arsize(13),
            axi_6_1_arburst                                   => hbm_axi_arburst(13),
            axi_6_1_arprot                                    => hbm_axi_arprot(13),
            axi_6_1_arqos                                     => hbm_axi_arqos(13),
            axi_6_1_aruser                                    => hbm_axi_aruser(13),
            axi_6_1_arvalid                                   => hbm_axi_arvalid(13),
            axi_6_1_arready                                   => hbm_axi_arready(13),
            axi_6_1_rid                                       => hbm_axi_rid(13),
            axi_6_1_rdata                                     => hbm_axi_rdata(13),
            axi_6_1_rresp                                     => hbm_axi_rresp(13),
            axi_6_1_rlast                                     => hbm_axi_rlast(13),
            axi_6_1_rvalid                                    => hbm_axi_rvalid(13),
            axi_6_1_rready                                    => hbm_axi_rready(13),

            axi_6_0_awid                                      => hbm_axi_awid(12),
            axi_6_0_awaddr                                    => hbm_axi_awaddr(12),
            axi_6_0_awlen                                     => hbm_axi_awlen(12),
            axi_6_0_awsize                                    => hbm_axi_awsize(12),
            axi_6_0_awburst                                   => hbm_axi_awburst(12),
            axi_6_0_awprot                                    => hbm_axi_awprot(12),
            axi_6_0_awqos                                     => hbm_axi_awqos(12),
            axi_6_0_awuser                                    => hbm_axi_awuser(12),
            axi_6_0_awvalid                                   => hbm_axi_awvalid(12),
            axi_6_0_awready                                   => hbm_axi_awready(12),
            axi_6_0_wdata                                     => hbm_axi_wdata(12),
            axi_6_0_wstrb                                     => hbm_axi_wstrb(12),
            axi_6_0_wlast                                     => hbm_axi_wlast(12),
            axi_6_0_wvalid                                    => hbm_axi_wvalid(12),
            axi_6_0_wready                                    => hbm_axi_wready(12),
            axi_6_0_bid                                       => hbm_axi_bid(12),
            axi_6_0_bresp                                     => hbm_axi_bresp(12),
            axi_6_0_bvalid                                    => hbm_axi_bvalid(12),
            axi_6_0_bready                                    => hbm_axi_bready(12),
            axi_6_0_arid                                      => hbm_axi_arid(12),
            axi_6_0_araddr                                    => hbm_axi_araddr(12),
            axi_6_0_arlen                                     => hbm_axi_arlen(12),
            axi_6_0_arsize                                    => hbm_axi_arsize(12),
            axi_6_0_arburst                                   => hbm_axi_arburst(12),
            axi_6_0_arprot                                    => hbm_axi_arprot(12),
            axi_6_0_arqos                                     => hbm_axi_arqos(12),
            axi_6_0_aruser                                    => hbm_axi_aruser(12),
            axi_6_0_arvalid                                   => hbm_axi_arvalid(12),
            axi_6_0_arready                                   => hbm_axi_arready(12),
            axi_6_0_rid                                       => hbm_axi_rid(12),
            axi_6_0_rdata                                     => hbm_axi_rdata(12),
            axi_6_0_rresp                                     => hbm_axi_rresp(12),
            axi_6_0_rlast                                     => hbm_axi_rlast(12),
            axi_6_0_rvalid                                    => hbm_axi_rvalid(12),
            axi_6_0_rready                                    => hbm_axi_rready(12),

            axi_7_1_awid                                      => hbm_axi_awid(15),
            axi_7_1_awaddr                                    => hbm_axi_awaddr(15),
            axi_7_1_awlen                                     => hbm_axi_awlen(15),
            axi_7_1_awsize                                    => hbm_axi_awsize(15),
            axi_7_1_awburst                                   => hbm_axi_awburst(15),
            axi_7_1_awprot                                    => hbm_axi_awprot(15),
            axi_7_1_awqos                                     => hbm_axi_awqos(15),
            axi_7_1_awuser                                    => hbm_axi_awuser(15),
            axi_7_1_awvalid                                   => hbm_axi_awvalid(15),
            axi_7_1_awready                                   => hbm_axi_awready(15),
            axi_7_1_wdata                                     => hbm_axi_wdata(15),
            axi_7_1_wstrb                                     => hbm_axi_wstrb(15),
            axi_7_1_wlast                                     => hbm_axi_wlast(15),
            axi_7_1_wvalid                                    => hbm_axi_wvalid(15),
            axi_7_1_wready                                    => hbm_axi_wready(15),
            axi_7_1_bid                                       => hbm_axi_bid(15),
            axi_7_1_bresp                                     => hbm_axi_bresp(15),
            axi_7_1_bvalid                                    => hbm_axi_bvalid(15),
            axi_7_1_bready                                    => hbm_axi_bready(15),
            axi_7_1_arid                                      => hbm_axi_arid(15),
            axi_7_1_araddr                                    => hbm_axi_araddr(15),
            axi_7_1_arlen                                     => hbm_axi_arlen(15),
            axi_7_1_arsize                                    => hbm_axi_arsize(15),
            axi_7_1_arburst                                   => hbm_axi_arburst(15),
            axi_7_1_arprot                                    => hbm_axi_arprot(15),
            axi_7_1_arqos                                     => hbm_axi_arqos(15),
            axi_7_1_aruser                                    => hbm_axi_aruser(15),
            axi_7_1_arvalid                                   => hbm_axi_arvalid(15),
            axi_7_1_arready                                   => hbm_axi_arready(15),
            axi_7_1_rid                                       => hbm_axi_rid(15),
            axi_7_1_rdata                                     => hbm_axi_rdata(15),
            axi_7_1_rresp                                     => hbm_axi_rresp(15),
            axi_7_1_rlast                                     => hbm_axi_rlast(15),
            axi_7_1_rvalid                                    => hbm_axi_rvalid(15),
            axi_7_1_rready                                    => hbm_axi_rready(15),

            axi_7_0_awid                                      => hbm_axi_awid(14),
            axi_7_0_awaddr                                    => hbm_axi_awaddr(14),
            axi_7_0_awlen                                     => hbm_axi_awlen(14),
            axi_7_0_awsize                                    => hbm_axi_awsize(14),
            axi_7_0_awburst                                   => hbm_axi_awburst(14),
            axi_7_0_awprot                                    => hbm_axi_awprot(14),
            axi_7_0_awqos                                     => hbm_axi_awqos(14),
            axi_7_0_awuser                                    => hbm_axi_awuser(14),
            axi_7_0_awvalid                                   => hbm_axi_awvalid(14),
            axi_7_0_awready                                   => hbm_axi_awready(14),
            axi_7_0_wdata                                     => hbm_axi_wdata(14),
            axi_7_0_wstrb                                     => hbm_axi_wstrb(14),
            axi_7_0_wlast                                     => hbm_axi_wlast(14),
            axi_7_0_wvalid                                    => hbm_axi_wvalid(14),
            axi_7_0_wready                                    => hbm_axi_wready(14),
            axi_7_0_bid                                       => hbm_axi_bid(14),
            axi_7_0_bresp                                     => hbm_axi_bresp(14),
            axi_7_0_bvalid                                    => hbm_axi_bvalid(14),
            axi_7_0_bready                                    => hbm_axi_bready(14),
            axi_7_0_arid                                      => hbm_axi_arid(14),
            axi_7_0_araddr                                    => hbm_axi_araddr(14),
            axi_7_0_arlen                                     => hbm_axi_arlen(14),
            axi_7_0_arsize                                    => hbm_axi_arsize(14),
            axi_7_0_arburst                                   => hbm_axi_arburst(14),
            axi_7_0_arprot                                    => hbm_axi_arprot(14),
            axi_7_0_arqos                                     => hbm_axi_arqos(14),
            axi_7_0_aruser                                    => hbm_axi_aruser(14),
            axi_7_0_arvalid                                   => hbm_axi_arvalid(14),
            axi_7_0_arready                                   => hbm_axi_arready(14),
            axi_7_0_rid                                       => hbm_axi_rid(14),
            axi_7_0_rdata                                     => hbm_axi_rdata(14),
            axi_7_0_rresp                                     => hbm_axi_rresp(14),
            axi_7_0_rlast                                     => hbm_axi_rlast(14),
            axi_7_0_rvalid                                    => hbm_axi_rvalid(14),
            axi_7_0_rready                                    => hbm_axi_rready(14)
        );
    else generate
        HBM_TOP_RESET_N    <= '0';
        HBM_TOP_WRST_N     <= '1';
        HBM_TOP_WRCK       <= '0';
        HBM_TOP_SHIFTWR    <= '0';
        HBM_TOP_CAPTUREWR  <= '0';
        HBM_TOP_UPDATEWR   <= '0';
        HBM_TOP_SELECTWIR  <= '0';
        HBM_TOP_WSI        <= '0';
    end generate;

    -- HBM BOTTOM
    hbm_bottom_g : if HBM_PORTS > 16 generate
        hbm_bottom_i : component hbm_bottom
        port map (
            pll_ref_clk                                       => HBM_BOTTOM_REF_CLK,
            ext_core_clk                                      => common_misc_out(2),
            ext_core_clk_locked                               => hbm_core_clk_locked(1),
            wmcrst_n_in                                       => hbm_wmcrst_n(1),
            hbm_only_reset_in                                 => hbm_rst_req(1),
            local_cal_success                                 => hbm_init_done(HBM_TOP_PORTS),
            local_cal_fail                                    => hbm_cal_fail(1),
            cattrip                                           => HBM_BOTTOM_CATTRIP,
            temp                                              => HBM_BOTTOM_TEMP,
            wso                                               => HBM_BOTTOM_WSO,
            reset_n                                           => HBM_BOTTOM_RESET_N,
            wrst_n                                            => HBM_BOTTOM_WRST_N,
            wrck                                              => HBM_BOTTOM_WRCK,
            shiftwr                                           => HBM_BOTTOM_SHIFTWR,
            capturewr                                         => HBM_BOTTOM_CAPTUREWR,
            updatewr                                          => HBM_BOTTOM_UPDATEWR,
            selectwir                                         => HBM_BOTTOM_SELECTWIR,
            wsi                                               => HBM_BOTTOM_WSI,

            wmc_clk_0_clk                                     => hbm_clk(HBM_TOP_PORTS+0),
            wmc_clk_1_clk                                     => hbm_clk(HBM_TOP_PORTS+2),
            wmcrst_n_0_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+0),
            wmcrst_n_1_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+2),

            axi_0_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+1),
            axi_0_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+1),
            axi_0_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+1),
            axi_0_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+1),
            axi_0_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+1),
            axi_0_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+1),
            axi_0_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+1),
            axi_0_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+1),
            axi_0_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+1),
            axi_0_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+1),
            axi_0_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+1),
            axi_0_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+1),
            axi_0_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+1),
            axi_0_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+1),
            axi_0_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+1),
            axi_0_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+1),
            axi_0_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+1),
            axi_0_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+1),
            axi_0_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+1),
            axi_0_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+1),
            axi_0_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+1),
            axi_0_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+1),
            axi_0_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+1),
            axi_0_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+1),
            axi_0_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+1),
            axi_0_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+1),
            axi_0_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+1),
            axi_0_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+1),
            axi_0_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+1),
            axi_0_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+1),
            axi_0_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+1),
            axi_0_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+1),
            axi_0_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+1),
            axi_0_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+1),
            axi_0_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+1),

            axi_0_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+0),
            axi_0_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+0),
            axi_0_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+0),
            axi_0_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+0),
            axi_0_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+0),
            axi_0_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+0),
            axi_0_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+0),
            axi_0_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+0),
            axi_0_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+0),
            axi_0_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+0),
            axi_0_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+0),
            axi_0_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+0),
            axi_0_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+0),
            axi_0_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+0),
            axi_0_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+0),
            axi_0_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+0),
            axi_0_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+0),
            axi_0_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+0),
            axi_0_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+0),
            axi_0_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+0),
            axi_0_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+0),
            axi_0_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+0),
            axi_0_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+0),
            axi_0_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+0),
            axi_0_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+0),
            axi_0_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+0),
            axi_0_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+0),
            axi_0_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+0),
            axi_0_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+0),
            axi_0_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+0),
            axi_0_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+0),
            axi_0_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+0),
            axi_0_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+0),
            axi_0_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+0),
            axi_0_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+0),

            axi_1_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+3),
            axi_1_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+3),
            axi_1_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+3),
            axi_1_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+3),
            axi_1_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+3),
            axi_1_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+3),
            axi_1_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+3),
            axi_1_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+3),
            axi_1_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+3),
            axi_1_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+3),
            axi_1_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+3),
            axi_1_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+3),
            axi_1_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+3),
            axi_1_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+3),
            axi_1_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+3),
            axi_1_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+3),
            axi_1_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+3),
            axi_1_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+3),
            axi_1_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+3),
            axi_1_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+3),
            axi_1_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+3),
            axi_1_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+3),
            axi_1_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+3),
            axi_1_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+3),
            axi_1_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+3),
            axi_1_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+3),
            axi_1_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+3),
            axi_1_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+3),
            axi_1_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+3),
            axi_1_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+3),
            axi_1_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+3),
            axi_1_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+3),
            axi_1_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+3),
            axi_1_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+3),
            axi_1_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+3),

            axi_1_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+2),
            axi_1_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+2),
            axi_1_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+2),
            axi_1_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+2),
            axi_1_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+2),
            axi_1_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+2),
            axi_1_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+2),
            axi_1_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+2),
            axi_1_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+2),
            axi_1_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+2),
            axi_1_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+2),
            axi_1_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+2),
            axi_1_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+2),
            axi_1_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+2),
            axi_1_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+2),
            axi_1_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+2),
            axi_1_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+2),
            axi_1_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+2),
            axi_1_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+2),
            axi_1_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+2),
            axi_1_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+2),
            axi_1_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+2),
            axi_1_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+2),
            axi_1_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+2),
            axi_1_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+2),
            axi_1_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+2),
            axi_1_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+2),
            axi_1_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+2),
            axi_1_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+2),
            axi_1_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+2),
            axi_1_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+2),
            axi_1_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+2),
            axi_1_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+2),
            axi_1_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+2),
            axi_1_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+2),

            wmc_clk_2_clk                                     => hbm_clk(HBM_TOP_PORTS+4),
            wmc_clk_3_clk                                     => hbm_clk(HBM_TOP_PORTS+6),
            wmcrst_n_2_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+4),
            wmcrst_n_3_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+6),

            axi_2_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+5),
            axi_2_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+5),
            axi_2_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+5),
            axi_2_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+5),
            axi_2_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+5),
            axi_2_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+5),
            axi_2_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+5),
            axi_2_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+5),
            axi_2_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+5),
            axi_2_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+5),
            axi_2_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+5),
            axi_2_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+5),
            axi_2_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+5),
            axi_2_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+5),
            axi_2_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+5),
            axi_2_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+5),
            axi_2_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+5),
            axi_2_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+5),
            axi_2_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+5),
            axi_2_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+5),
            axi_2_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+5),
            axi_2_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+5),
            axi_2_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+5),
            axi_2_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+5),
            axi_2_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+5),
            axi_2_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+5),
            axi_2_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+5),
            axi_2_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+5),
            axi_2_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+5),
            axi_2_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+5),
            axi_2_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+5),
            axi_2_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+5),
            axi_2_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+5),
            axi_2_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+5),
            axi_2_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+5),

            axi_2_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+4),
            axi_2_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+4),
            axi_2_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+4),
            axi_2_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+4),
            axi_2_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+4),
            axi_2_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+4),
            axi_2_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+4),
            axi_2_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+4),
            axi_2_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+4),
            axi_2_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+4),
            axi_2_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+4),
            axi_2_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+4),
            axi_2_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+4),
            axi_2_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+4),
            axi_2_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+4),
            axi_2_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+4),
            axi_2_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+4),
            axi_2_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+4),
            axi_2_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+4),
            axi_2_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+4),
            axi_2_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+4),
            axi_2_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+4),
            axi_2_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+4),
            axi_2_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+4),
            axi_2_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+4),
            axi_2_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+4),
            axi_2_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+4),
            axi_2_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+4),
            axi_2_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+4),
            axi_2_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+4),
            axi_2_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+4),
            axi_2_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+4),
            axi_2_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+4),
            axi_2_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+4),
            axi_2_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+4),

            axi_3_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+7),
            axi_3_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+7),
            axi_3_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+7),
            axi_3_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+7),
            axi_3_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+7),
            axi_3_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+7),
            axi_3_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+7),
            axi_3_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+7),
            axi_3_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+7),
            axi_3_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+7),
            axi_3_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+7),
            axi_3_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+7),
            axi_3_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+7),
            axi_3_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+7),
            axi_3_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+7),
            axi_3_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+7),
            axi_3_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+7),
            axi_3_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+7),
            axi_3_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+7),
            axi_3_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+7),
            axi_3_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+7),
            axi_3_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+7),
            axi_3_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+7),
            axi_3_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+7),
            axi_3_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+7),
            axi_3_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+7),
            axi_3_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+7),
            axi_3_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+7),
            axi_3_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+7),
            axi_3_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+7),
            axi_3_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+7),
            axi_3_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+7),
            axi_3_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+7),
            axi_3_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+7),
            axi_3_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+7),

            axi_3_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+6),
            axi_3_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+6),
            axi_3_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+6),
            axi_3_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+6),
            axi_3_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+6),
            axi_3_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+6),
            axi_3_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+6),
            axi_3_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+6),
            axi_3_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+6),
            axi_3_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+6),
            axi_3_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+6),
            axi_3_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+6),
            axi_3_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+6),
            axi_3_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+6),
            axi_3_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+6),
            axi_3_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+6),
            axi_3_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+6),
            axi_3_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+6),
            axi_3_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+6),
            axi_3_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+6),
            axi_3_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+6),
            axi_3_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+6),
            axi_3_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+6),
            axi_3_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+6),
            axi_3_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+6),
            axi_3_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+6),
            axi_3_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+6),
            axi_3_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+6),
            axi_3_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+6),
            axi_3_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+6),
            axi_3_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+6),
            axi_3_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+6),
            axi_3_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+6),
            axi_3_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+6),
            axi_3_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+6),

            wmc_clk_4_clk                                     => hbm_clk(HBM_TOP_PORTS+8),
            wmc_clk_5_clk                                     => hbm_clk(HBM_TOP_PORTS+10),
            wmcrst_n_4_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+8),
            wmcrst_n_5_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+10),

            axi_4_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+9),
            axi_4_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+9),
            axi_4_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+9),
            axi_4_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+9),
            axi_4_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+9),
            axi_4_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+9),
            axi_4_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+9),
            axi_4_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+9),
            axi_4_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+9),
            axi_4_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+9),
            axi_4_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+9),
            axi_4_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+9),
            axi_4_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+9),
            axi_4_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+9),
            axi_4_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+9),
            axi_4_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+9),
            axi_4_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+9),
            axi_4_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+9),
            axi_4_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+9),
            axi_4_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+9),
            axi_4_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+9),
            axi_4_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+9),
            axi_4_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+9),
            axi_4_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+9),
            axi_4_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+9),
            axi_4_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+9),
            axi_4_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+9),
            axi_4_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+9),
            axi_4_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+9),
            axi_4_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+9),
            axi_4_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+9),
            axi_4_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+9),
            axi_4_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+9),
            axi_4_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+9),
            axi_4_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+9),

            axi_4_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+8),
            axi_4_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+8),
            axi_4_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+8),
            axi_4_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+8),
            axi_4_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+8),
            axi_4_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+8),
            axi_4_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+8),
            axi_4_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+8),
            axi_4_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+8),
            axi_4_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+8),
            axi_4_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+8),
            axi_4_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+8),
            axi_4_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+8),
            axi_4_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+8),
            axi_4_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+8),
            axi_4_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+8),
            axi_4_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+8),
            axi_4_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+8),
            axi_4_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+8),
            axi_4_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+8),
            axi_4_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+8),
            axi_4_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+8),
            axi_4_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+8),
            axi_4_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+8),
            axi_4_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+8),
            axi_4_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+8),
            axi_4_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+8),
            axi_4_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+8),
            axi_4_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+8),
            axi_4_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+8),
            axi_4_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+8),
            axi_4_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+8),
            axi_4_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+8),
            axi_4_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+8),
            axi_4_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+8),

            axi_5_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+11),
            axi_5_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+11),
            axi_5_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+11),
            axi_5_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+11),
            axi_5_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+11),
            axi_5_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+11),
            axi_5_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+11),
            axi_5_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+11),
            axi_5_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+11),
            axi_5_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+11),
            axi_5_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+11),
            axi_5_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+11),
            axi_5_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+11),
            axi_5_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+11),
            axi_5_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+11),
            axi_5_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+11),
            axi_5_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+11),
            axi_5_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+11),
            axi_5_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+11),
            axi_5_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+11),
            axi_5_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+11),
            axi_5_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+11),
            axi_5_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+11),
            axi_5_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+11),
            axi_5_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+11),
            axi_5_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+11),
            axi_5_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+11),
            axi_5_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+11),
            axi_5_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+11),
            axi_5_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+11),
            axi_5_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+11),
            axi_5_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+11),
            axi_5_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+11),
            axi_5_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+11),
            axi_5_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+11),

            axi_5_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+10),
            axi_5_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+10),
            axi_5_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+10),
            axi_5_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+10),
            axi_5_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+10),
            axi_5_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+10),
            axi_5_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+10),
            axi_5_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+10),
            axi_5_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+10),
            axi_5_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+10),
            axi_5_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+10),
            axi_5_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+10),
            axi_5_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+10),
            axi_5_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+10),
            axi_5_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+10),
            axi_5_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+10),
            axi_5_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+10),
            axi_5_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+10),
            axi_5_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+10),
            axi_5_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+10),
            axi_5_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+10),
            axi_5_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+10),
            axi_5_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+10),
            axi_5_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+10),
            axi_5_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+10),
            axi_5_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+10),
            axi_5_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+10),
            axi_5_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+10),
            axi_5_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+10),
            axi_5_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+10),
            axi_5_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+10),
            axi_5_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+10),
            axi_5_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+10),
            axi_5_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+10),
            axi_5_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+10),

            wmc_clk_6_clk                                     => hbm_clk(HBM_TOP_PORTS+12),
            wmc_clk_7_clk                                     => hbm_clk(HBM_TOP_PORTS+14),
            wmcrst_n_6_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+12),
            wmcrst_n_7_reset_n                                => hbm_rst_n(HBM_TOP_PORTS+14),

            axi_6_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+13),
            axi_6_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+13),
            axi_6_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+13),
            axi_6_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+13),
            axi_6_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+13),
            axi_6_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+13),
            axi_6_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+13),
            axi_6_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+13),
            axi_6_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+13),
            axi_6_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+13),
            axi_6_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+13),
            axi_6_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+13),
            axi_6_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+13),
            axi_6_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+13),
            axi_6_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+13),
            axi_6_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+13),
            axi_6_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+13),
            axi_6_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+13),
            axi_6_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+13),
            axi_6_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+13),
            axi_6_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+13),
            axi_6_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+13),
            axi_6_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+13),
            axi_6_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+13),
            axi_6_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+13),
            axi_6_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+13),
            axi_6_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+13),
            axi_6_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+13),
            axi_6_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+13),
            axi_6_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+13),
            axi_6_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+13),
            axi_6_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+13),
            axi_6_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+13),
            axi_6_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+13),
            axi_6_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+13),

            axi_6_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+12),
            axi_6_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+12),
            axi_6_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+12),
            axi_6_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+12),
            axi_6_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+12),
            axi_6_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+12),
            axi_6_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+12),
            axi_6_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+12),
            axi_6_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+12),
            axi_6_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+12),
            axi_6_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+12),
            axi_6_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+12),
            axi_6_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+12),
            axi_6_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+12),
            axi_6_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+12),
            axi_6_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+12),
            axi_6_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+12),
            axi_6_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+12),
            axi_6_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+12),
            axi_6_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+12),
            axi_6_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+12),
            axi_6_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+12),
            axi_6_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+12),
            axi_6_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+12),
            axi_6_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+12),
            axi_6_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+12),
            axi_6_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+12),
            axi_6_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+12),
            axi_6_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+12),
            axi_6_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+12),
            axi_6_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+12),
            axi_6_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+12),
            axi_6_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+12),
            axi_6_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+12),
            axi_6_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+12),

            axi_7_1_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+15),
            axi_7_1_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+15),
            axi_7_1_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+15),
            axi_7_1_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+15),
            axi_7_1_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+15),
            axi_7_1_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+15),
            axi_7_1_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+15),
            axi_7_1_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+15),
            axi_7_1_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+15),
            axi_7_1_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+15),
            axi_7_1_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+15),
            axi_7_1_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+15),
            axi_7_1_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+15),
            axi_7_1_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+15),
            axi_7_1_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+15),
            axi_7_1_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+15),
            axi_7_1_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+15),
            axi_7_1_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+15),
            axi_7_1_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+15),
            axi_7_1_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+15),
            axi_7_1_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+15),
            axi_7_1_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+15),
            axi_7_1_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+15),
            axi_7_1_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+15),
            axi_7_1_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+15),
            axi_7_1_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+15),
            axi_7_1_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+15),
            axi_7_1_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+15),
            axi_7_1_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+15),
            axi_7_1_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+15),
            axi_7_1_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+15),
            axi_7_1_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+15),
            axi_7_1_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+15),
            axi_7_1_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+15),
            axi_7_1_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+15),

            axi_7_0_awid                                      => hbm_axi_awid(HBM_TOP_PORTS+14),
            axi_7_0_awaddr                                    => hbm_axi_awaddr(HBM_TOP_PORTS+14),
            axi_7_0_awlen                                     => hbm_axi_awlen(HBM_TOP_PORTS+14),
            axi_7_0_awsize                                    => hbm_axi_awsize(HBM_TOP_PORTS+14),
            axi_7_0_awburst                                   => hbm_axi_awburst(HBM_TOP_PORTS+14),
            axi_7_0_awprot                                    => hbm_axi_awprot(HBM_TOP_PORTS+14),
            axi_7_0_awqos                                     => hbm_axi_awqos(HBM_TOP_PORTS+14),
            axi_7_0_awuser                                    => hbm_axi_awuser(HBM_TOP_PORTS+14),
            axi_7_0_awvalid                                   => hbm_axi_awvalid(HBM_TOP_PORTS+14),
            axi_7_0_awready                                   => hbm_axi_awready(HBM_TOP_PORTS+14),
            axi_7_0_wdata                                     => hbm_axi_wdata(HBM_TOP_PORTS+14),
            axi_7_0_wstrb                                     => hbm_axi_wstrb(HBM_TOP_PORTS+14),
            axi_7_0_wlast                                     => hbm_axi_wlast(HBM_TOP_PORTS+14),
            axi_7_0_wvalid                                    => hbm_axi_wvalid(HBM_TOP_PORTS+14),
            axi_7_0_wready                                    => hbm_axi_wready(HBM_TOP_PORTS+14),
            axi_7_0_bid                                       => hbm_axi_bid(HBM_TOP_PORTS+14),
            axi_7_0_bresp                                     => hbm_axi_bresp(HBM_TOP_PORTS+14),
            axi_7_0_bvalid                                    => hbm_axi_bvalid(HBM_TOP_PORTS+14),
            axi_7_0_bready                                    => hbm_axi_bready(HBM_TOP_PORTS+14),
            axi_7_0_arid                                      => hbm_axi_arid(HBM_TOP_PORTS+14),
            axi_7_0_araddr                                    => hbm_axi_araddr(HBM_TOP_PORTS+14),
            axi_7_0_arlen                                     => hbm_axi_arlen(HBM_TOP_PORTS+14),
            axi_7_0_arsize                                    => hbm_axi_arsize(HBM_TOP_PORTS+14),
            axi_7_0_arburst                                   => hbm_axi_arburst(HBM_TOP_PORTS+14),
            axi_7_0_arprot                                    => hbm_axi_arprot(HBM_TOP_PORTS+14),
            axi_7_0_arqos                                     => hbm_axi_arqos(HBM_TOP_PORTS+14),
            axi_7_0_aruser                                    => hbm_axi_aruser(HBM_TOP_PORTS+14),
            axi_7_0_arvalid                                   => hbm_axi_arvalid(HBM_TOP_PORTS+14),
            axi_7_0_arready                                   => hbm_axi_arready(HBM_TOP_PORTS+14),
            axi_7_0_rid                                       => hbm_axi_rid(HBM_TOP_PORTS+14),
            axi_7_0_rdata                                     => hbm_axi_rdata(HBM_TOP_PORTS+14),
            axi_7_0_rresp                                     => hbm_axi_rresp(HBM_TOP_PORTS+14),
            axi_7_0_rlast                                     => hbm_axi_rlast(HBM_TOP_PORTS+14),
            axi_7_0_rvalid                                    => hbm_axi_rvalid(HBM_TOP_PORTS+14),
            axi_7_0_rready                                    => hbm_axi_rready(HBM_TOP_PORTS+14)
        );
    else generate
        HBM_BOTTOM_RESET_N    <= '0';
        HBM_BOTTOM_WRST_N     <= '1';
        HBM_BOTTOM_WRCK       <= '0';
        HBM_BOTTOM_SHIFTWR    <= '0';
        HBM_BOTTOM_CAPTUREWR  <= '0';
        HBM_BOTTOM_UPDATEWR   <= '0';
        HBM_BOTTOM_SELECTWIR  <= '0';
        HBM_BOTTOM_WSI        <= '0';
    end generate;

    hbm_en_g: if HBM_PORTS > 0 generate
        hbm_clk_rst_gen : for i in (HBM_PORTS)/2-1 downto 0 generate
            hbm_clk(2*i+1)   <= hbm_clk(2*i);
            hbm_rst_n(2*i+1) <= hbm_rst_n(2*i);
        end generate;

        hbm_init_done_gen : for i in 1 to HBM_TOP_PORTS-1 generate
            hbm_init_done(i) <= hbm_init_done(0);
            hbm_bottom_init_done_g : if HBM_PORTS > 16 generate
                hbm_init_done(HBM_TOP_PORTS+i) <= hbm_init_done(HBM_TOP_PORTS);
            end generate;
        end generate;
    end generate;

    -- =========================================================================
    --  BOOT SPI
    -- =========================================================================

    boot_i : entity work.MI32_SPI_BRIDGE_TOP
    port map(
        CLK         => boot_mi_clk, -- 100 MHz
        RESET       => boot_mi_reset,

        SPI_MISO    => SPI_MISO,
        SPI_MOSI    => SPI_MOSI,
        SPI_S_CLK   => SPI_SCLK,
        SPI_CS_L    => SPI_CS_L,

        MI_DWR      => boot_mi_dwr,
        MI_ADDR     => boot_mi_addr,
        MI_RD       => boot_mi_rd,
        MI_WR       => boot_mi_wr,
        MI_BE       => boot_mi_be,
        MI_DRD      => boot_mi_drd,
        MI_ARDY     => boot_mi_ardy,
        MI_DRDY     => boot_mi_drdy
    );
    BMC_NINIT_DONE <= boot_mi_reset;

    -- =========================================================================
    --  QSFP MAPPING
    -- =========================================================================
    eth_refclk_p <= ETILE_REFCLK_156M & ETILE_REFCLK_156M & ETILE_REFCLK_156M & ETILE_REFCLK_156M;
    eth_refclk_n <= (others => '0'); -- Quartus will handle the connection itself

    eth_rx_p <= QSFP3_RX_P & QSFP2_RX_P & QSFP1_RX_P & QSFP0_RX_P;
    eth_rx_n <= QSFP3_RX_N & QSFP2_RX_N & QSFP1_RX_N & QSFP0_RX_N;

    QSFP0_TX_P <= eth_tx_p(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP0_TX_N <= eth_tx_n(1*ETH_LANES-1 downto 0*ETH_LANES);
    QSFP1_TX_P <= eth_tx_p(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP1_TX_N <= eth_tx_n(2*ETH_LANES-1 downto 1*ETH_LANES);
    QSFP2_TX_P <= eth_tx_p(3*ETH_LANES-1 downto 2*ETH_LANES);
    QSFP2_TX_N <= eth_tx_n(3*ETH_LANES-1 downto 2*ETH_LANES);
    QSFP3_TX_P <= eth_tx_p(4*ETH_LANES-1 downto 3*ETH_LANES);
    QSFP3_TX_N <= eth_tx_n(4*ETH_LANES-1 downto 3*ETH_LANES);

end architecture;
