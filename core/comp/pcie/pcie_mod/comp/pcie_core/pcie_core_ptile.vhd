-- pcie_core_ptile.vhd: PCIe module
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;


-- ============================================================================
--                                Description
-- ============================================================================

-- This is the specific wrapper around the Intel PCIe IP core P-Tile.
--
architecture PTILE of PCIE_CORE is

    component ptile_pcie_1x16 is
        port (
            P0_RX_ST_READY_I             : in  std_logic                      := 'X';
            P0_RX_ST_SOP_O               : out std_logic_vector(1 downto 0);
            P0_RX_ST_EOP_O               : out std_logic_vector(1 downto 0);
            P0_RX_ST_DATA_O              : out std_logic_vector(511 downto 0);
            P0_RX_ST_VALID_O             : out std_logic_vector(1 downto 0);
            P0_RX_ST_EMPTY_O             : out std_logic_vector(5 downto 0);
            P0_RX_ST_HDR_O               : out std_logic_vector(255 downto 0);
            P0_RX_ST_TLP_PRFX_O          : out std_logic_vector(63 downto 0);
            P0_RX_ST_BAR_RANGE_O         : out std_logic_vector(5 downto 0);
            P0_RX_ST_TLP_ABORT_O         : out std_logic_vector(1 downto 0);
            P0_RX_PAR_ERR_O              : out std_logic;
            P0_TX_ST_SOP_I               : in  std_logic_vector(1 downto 0)   := (others => 'X');
            P0_TX_ST_EOP_I               : in  std_logic_vector(1 downto 0)   := (others => 'X');
            P0_TX_ST_DATA_I              : in  std_logic_vector(511 downto 0) := (others => 'X');
            P0_TX_ST_VALID_I             : in  std_logic_vector(1 downto 0)   := (others => 'X');
            P0_TX_ST_ERR_I               : in  std_logic_vector(1 downto 0)   := (others => 'X');
            P0_TX_ST_READY_O             : out std_logic;
            P0_TX_ST_HDR_I               : in  std_logic_vector(255 downto 0) := (others => 'X');
            P0_TX_ST_TLP_PRFX_I          : in  std_logic_vector(63 downto 0)  := (others => 'X');
            P0_TX_PAR_ERR_O              : out std_logic;
            P0_TX_CDTS_LIMIT_O           : out std_logic_vector(15 downto 0);
            P0_TX_CDTS_LIMIT_TDM_IDX_O   : out std_logic_vector(2 downto 0);
            P0_TL_CFG_FUNC_O             : out std_logic_vector(2 downto 0);
            P0_TL_CFG_ADD_O              : out std_logic_vector(4 downto 0);
            P0_TL_CFG_CTL_O              : out std_logic_vector(15 downto 0);
            P0_DL_TIMER_UPDATE_O         : out std_logic;
            P0_RESET_STATUS_N            : out std_logic;
            P0_PIN_PERST_N               : out std_logic;
            P0_LINK_UP_O                 : out std_logic;
            P0_DL_UP_O                   : out std_logic;
            P0_SURPRISE_DOWN_ERR_O       : out std_logic;
            P0_PM_STATE_O                : out std_logic_vector(2 downto 0);
            P0_LTSSM_STATE_O             : out std_logic_vector(5 downto 0);
            P0_PM_DSTATE_O               : out std_logic_vector(31 downto 0);
            P0_APPS_PM_XMT_PME_I         : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P0_APP_REQ_RETRY_EN_I        : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P0_CII_HDR_POISONED_O        : out std_logic;
            P0_CII_OVERRIDE_EN_I         : in  std_logic                      := 'X';
            P0_CII_HDR_FIRST_BE_O        : out std_logic_vector(3 downto 0);
            P0_CII_DOUT_O                : out std_logic_vector(31 downto 0);
            P0_CII_HALT_I                : in  std_logic                      := 'X';
            P0_CII_REQ_O                 : out std_logic;
            P0_CII_ADDR_O                : out std_logic_vector(9 downto 0);
            P0_CII_WR_O                  : out std_logic;
            P0_CII_OVERRIDE_DIN_I        : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RX_N_IN0                     : in  std_logic                      := 'X';
            RX_N_IN1                     : in  std_logic                      := 'X';
            RX_N_IN2                     : in  std_logic                      := 'X';
            RX_N_IN3                     : in  std_logic                      := 'X';
            RX_N_IN4                     : in  std_logic                      := 'X';
            RX_N_IN5                     : in  std_logic                      := 'X';
            RX_N_IN6                     : in  std_logic                      := 'X';
            RX_N_IN7                     : in  std_logic                      := 'X';
            RX_N_IN8                     : in  std_logic                      := 'X';
            RX_N_IN9                     : in  std_logic                      := 'X';
            RX_N_IN10                    : in  std_logic                      := 'X';
            RX_N_IN11                    : in  std_logic                      := 'X';
            RX_N_IN12                    : in  std_logic                      := 'X';
            RX_N_IN13                    : in  std_logic                      := 'X';
            RX_N_IN14                    : in  std_logic                      := 'X';
            RX_N_IN15                    : in  std_logic                      := 'X';
            RX_P_IN0                     : in  std_logic                      := 'X';
            RX_P_IN1                     : in  std_logic                      := 'X';
            RX_P_IN2                     : in  std_logic                      := 'X';
            RX_P_IN3                     : in  std_logic                      := 'X';
            RX_P_IN4                     : in  std_logic                      := 'X';
            RX_P_IN5                     : in  std_logic                      := 'X';
            RX_P_IN6                     : in  std_logic                      := 'X';
            RX_P_IN7                     : in  std_logic                      := 'X';
            RX_P_IN8                     : in  std_logic                      := 'X';
            RX_P_IN9                     : in  std_logic                      := 'X';
            RX_P_IN10                    : in  std_logic                      := 'X';
            RX_P_IN11                    : in  std_logic                      := 'X';
            RX_P_IN12                    : in  std_logic                      := 'X';
            RX_P_IN13                    : in  std_logic                      := 'X';
            RX_P_IN14                    : in  std_logic                      := 'X';
            RX_P_IN15                    : in  std_logic                      := 'X';
            TX_N_OUT0                    : out std_logic;
            TX_N_OUT1                    : out std_logic;
            TX_N_OUT2                    : out std_logic;
            TX_N_OUT3                    : out std_logic;
            TX_N_OUT4                    : out std_logic;
            TX_N_OUT5                    : out std_logic;
            TX_N_OUT6                    : out std_logic;
            TX_N_OUT7                    : out std_logic;
            TX_N_OUT8                    : out std_logic;
            TX_N_OUT9                    : out std_logic;
            TX_N_OUT10                   : out std_logic;
            TX_N_OUT11                   : out std_logic;
            TX_N_OUT12                   : out std_logic;
            TX_N_OUT13                   : out std_logic;
            TX_N_OUT14                   : out std_logic;
            TX_N_OUT15                   : out std_logic;
            TX_P_OUT0                    : out std_logic;
            TX_P_OUT1                    : out std_logic;
            TX_P_OUT2                    : out std_logic;
            TX_P_OUT3                    : out std_logic;
            TX_P_OUT4                    : out std_logic;
            TX_P_OUT5                    : out std_logic;
            TX_P_OUT6                    : out std_logic;
            TX_P_OUT7                    : out std_logic;
            TX_P_OUT8                    : out std_logic;
            TX_P_OUT9                    : out std_logic;
            TX_P_OUT10                   : out std_logic;
            TX_P_OUT11                   : out std_logic;
            TX_P_OUT12                   : out std_logic;
            TX_P_OUT13                   : out std_logic;
            TX_P_OUT14                   : out std_logic;
            TX_P_OUT15                   : out std_logic;
            CORECLKOUT_HIP               : out std_logic;
            REFCLK0                      : in  std_logic                      := 'X';
            REFCLK1                      : in  std_logic                      := 'X';
            PIN_PERST_N                  : in  std_logic                      := 'X';
            NINIT_DONE                   : in  std_logic                      := 'X'
        );
    end component;

    component ptile_pcie_2x8 is
        port (
            P0_RX_ST_READY_I           : in  std_logic                      := 'X';
            P0_RX_ST_SOP_O             : out std_logic_vector(0 downto 0);
            P0_RX_ST_EOP_O             : out std_logic_vector(0 downto 0);
            P0_RX_ST_DATA_O            : out std_logic_vector(255 downto 0);
            P0_RX_ST_VALID_O           : out std_logic_vector(0 downto 0);
            P0_RX_ST_EMPTY_O           : out std_logic_vector(2 downto 0);
            P0_RX_ST_HDR_O             : out std_logic_vector(127 downto 0);
            P0_RX_ST_TLP_PRFX_O        : out std_logic_vector(31 downto 0);
            P0_RX_ST_BAR_RANGE_O       : out std_logic_vector(2 downto 0);
            P0_RX_ST_TLP_ABORT_O       : out std_logic_vector(0 downto 0);
            P0_RX_PAR_ERR_O            : out std_logic;
            P0_TX_ST_SOP_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P0_TX_ST_EOP_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P0_TX_ST_DATA_I            : in  std_logic_vector(255 downto 0) := (others => 'X');
            P0_TX_ST_VALID_I           : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P0_TX_ST_ERR_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P0_TX_ST_READY_O           : out std_logic;
            P0_TX_ST_HDR_I             : in  std_logic_vector(127 downto 0) := (others => 'X');
            P0_TX_ST_TLP_PRFX_I        : in  std_logic_vector(31 downto 0)  := (others => 'X');
            P0_TX_PAR_ERR_O            : out std_logic;
            P0_TX_CDTS_LIMIT_O         : out std_logic_vector(15 downto 0);
            P0_TX_CDTS_LIMIT_TDM_IDX_O : out std_logic_vector(2 downto 0);
            P0_TL_CFG_FUNC_O           : out std_logic_vector(2 downto 0);
            P0_TL_CFG_ADD_O            : out std_logic_vector(4 downto 0);
            P0_TL_CFG_CTL_O            : out std_logic_vector(15 downto 0);
            P0_DL_TIMER_UPDATE_O       : out std_logic;
            P1_RX_ST_READY_I           : in  std_logic                      := 'X';
            P1_RX_ST_SOP_O             : out std_logic_vector(0 downto 0);
            P1_RX_ST_EOP_O             : out std_logic_vector(0 downto 0);
            P1_RX_ST_DATA_O            : out std_logic_vector(255 downto 0);
            P1_RX_ST_VALID_O           : out std_logic_vector(0 downto 0);
            P1_RX_ST_EMPTY_O           : out std_logic_vector(2 downto 0);
            P1_RX_ST_HDR_O             : out std_logic_vector(127 downto 0);
            P1_RX_ST_TLP_PRFX_O        : out std_logic_vector(31 downto 0);
            P1_RX_ST_BAR_RANGE_O       : out std_logic_vector(2 downto 0);
            P1_RX_ST_TLP_ABORT_O       : out std_logic_vector(0 downto 0);
            P1_RX_PAR_ERR_O            : out std_logic;
            P1_TX_ST_SOP_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P1_TX_ST_EOP_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P1_TX_ST_DATA_I            : in  std_logic_vector(255 downto 0) := (others => 'X');
            P1_TX_ST_VALID_I           : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P1_TX_ST_ERR_I             : in  std_logic_vector(0 downto 0)   := (others => 'X');
            P1_TX_ST_READY_O           : out std_logic;
            P1_TX_ST_HDR_I             : in  std_logic_vector(127 downto 0) := (others => 'X');
            P1_TX_ST_TLP_PRFX_I        : in  std_logic_vector(31 downto 0)  := (others => 'X');
            P1_TX_PAR_ERR_O            : out std_logic;
            P1_TX_CDTS_LIMIT_O         : out std_logic_vector(15 downto 0);
            P1_TX_CDTS_LIMIT_TDM_IDX_O : out std_logic_vector(2 downto 0);
            P1_TL_CFG_FUNC_O           : out std_logic_vector(2 downto 0);
            P1_TL_CFG_ADD_O            : out std_logic_vector(4 downto 0);
            P1_TL_CFG_CTL_O            : out std_logic_vector(15 downto 0);
            P1_DL_TIMER_UPDATE_O       : out std_logic;
            P1_RESET_STATUS_N          : out std_logic;
            P1_PIN_PERST_N             : out std_logic;
            P1_LINK_UP_O               : out std_logic;
            P1_DL_UP_O                 : out std_logic;
            P1_SURPRISE_DOWN_ERR_O     : out std_logic;
            P1_PM_STATE_O              : out std_logic_vector(2 downto 0);
            P1_LTSSM_STATE_O           : out std_logic_vector(5 downto 0);
            P1_PM_DSTATE_O             : out std_logic_vector(31 downto 0);
            P1_APPS_PM_XMT_PME_I       : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P1_APP_REQ_RETRY_EN_I      : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P1_CII_HDR_POISONED_O      : out std_logic;
            P1_CII_OVERRIDE_EN_I       : in  std_logic                      := 'X';
            P1_CII_HDR_FIRST_BE_O      : out std_logic_vector(3 downto 0);
            P1_CII_DOUT_O              : out std_logic_vector(31 downto 0);
            P1_CII_HALT_I              : in  std_logic                      := 'X';
            P1_CII_REQ_O               : out std_logic;
            P1_CII_ADDR_O              : out std_logic_vector(9 downto 0);
            P1_CII_WR_O                : out std_logic;
            P1_CII_OVERRIDE_DIN_I      : in  std_logic_vector(31 downto 0)  := (others => 'X');
            P0_RESET_STATUS_N          : out std_logic;
            P0_PIN_PERST_N             : out std_logic;
            P0_LINK_UP_O               : out std_logic;
            P0_DL_UP_O                 : out std_logic;
            P0_SURPRISE_DOWN_ERR_O     : out std_logic;
            P0_PM_STATE_O              : out std_logic_vector(2 downto 0);
            P0_LTSSM_STATE_O           : out std_logic_vector(5 downto 0);
            P0_PM_DSTATE_O             : out std_logic_vector(31 downto 0);
            P0_APPS_PM_XMT_PME_I       : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P0_APP_REQ_RETRY_EN_I      : in  std_logic_vector(7 downto 0)   := (others => 'X');
            P0_CII_HDR_POISONED_O      : out std_logic;
            P0_CII_OVERRIDE_EN_I       : in  std_logic                      := 'X';
            P0_CII_HDR_FIRST_BE_O      : out std_logic_vector(3 downto 0);
            P0_CII_DOUT_O              : out std_logic_vector(31 downto 0);
            P0_CII_HALT_I              : in  std_logic                      := 'X';
            P0_CII_REQ_O               : out std_logic;
            P0_CII_ADDR_O              : out std_logic_vector(9 downto 0);
            P0_CII_WR_O                : out std_logic;
            P0_CII_OVERRIDE_DIN_I      : in  std_logic_vector(31 downto 0)  := (others => 'X');
            RX_N_IN0                   : in  std_logic                      := 'X';
            RX_N_IN1                   : in  std_logic                      := 'X';
            RX_N_IN2                   : in  std_logic                      := 'X';
            RX_N_IN3                   : in  std_logic                      := 'X';
            RX_N_IN4                   : in  std_logic                      := 'X';
            RX_N_IN5                   : in  std_logic                      := 'X';
            RX_N_IN6                   : in  std_logic                      := 'X';
            RX_N_IN7                   : in  std_logic                      := 'X';
            RX_N_IN8                   : in  std_logic                      := 'X';
            RX_N_IN9                   : in  std_logic                      := 'X';
            RX_N_IN10                  : in  std_logic                      := 'X';
            RX_N_IN11                  : in  std_logic                      := 'X';
            RX_N_IN12                  : in  std_logic                      := 'X';
            RX_N_IN13                  : in  std_logic                      := 'X';
            RX_N_IN14                  : in  std_logic                      := 'X';
            RX_N_IN15                  : in  std_logic                      := 'X';
            RX_P_IN0                   : in  std_logic                      := 'X';
            RX_P_IN1                   : in  std_logic                      := 'X';
            RX_P_IN2                   : in  std_logic                      := 'X';
            RX_P_IN3                   : in  std_logic                      := 'X';
            RX_P_IN4                   : in  std_logic                      := 'X';
            RX_P_IN5                   : in  std_logic                      := 'X';
            RX_P_IN6                   : in  std_logic                      := 'X';
            RX_P_IN7                   : in  std_logic                      := 'X';
            RX_P_IN8                   : in  std_logic                      := 'X';
            RX_P_IN9                   : in  std_logic                      := 'X';
            RX_P_IN10                  : in  std_logic                      := 'X';
            RX_P_IN11                  : in  std_logic                      := 'X';
            RX_P_IN12                  : in  std_logic                      := 'X';
            RX_P_IN13                  : in  std_logic                      := 'X';
            RX_P_IN14                  : in  std_logic                      := 'X';
            RX_P_IN15                  : in  std_logic                      := 'X';
            TX_N_OUT0                  : out std_logic;
            TX_N_OUT1                  : out std_logic;
            TX_N_OUT2                  : out std_logic;
            TX_N_OUT3                  : out std_logic;
            TX_N_OUT4                  : out std_logic;
            TX_N_OUT5                  : out std_logic;
            TX_N_OUT6                  : out std_logic;
            TX_N_OUT7                  : out std_logic;
            TX_N_OUT8                  : out std_logic;
            TX_N_OUT9                  : out std_logic;
            TX_N_OUT10                 : out std_logic;
            TX_N_OUT11                 : out std_logic;
            TX_N_OUT12                 : out std_logic;
            TX_N_OUT13                 : out std_logic;
            TX_N_OUT14                 : out std_logic;
            TX_N_OUT15                 : out std_logic;
            TX_P_OUT0                  : out std_logic;
            TX_P_OUT1                  : out std_logic;
            TX_P_OUT2                  : out std_logic;
            TX_P_OUT3                  : out std_logic;
            TX_P_OUT4                  : out std_logic;
            TX_P_OUT5                  : out std_logic;
            TX_P_OUT6                  : out std_logic;
            TX_P_OUT7                  : out std_logic;
            TX_P_OUT8                  : out std_logic;
            TX_P_OUT9                  : out std_logic;
            TX_P_OUT10                 : out std_logic;
            TX_P_OUT11                 : out std_logic;
            TX_P_OUT12                 : out std_logic;
            TX_P_OUT13                 : out std_logic;
            TX_P_OUT14                 : out std_logic;
            TX_P_OUT15                 : out std_logic;
            CORECLKOUT_HIP             : out std_logic;
            REFCLK0                    : in  std_logic                      := 'X';
            REFCLK1                    : in  std_logic                      := 'X';
            PIN_PERST_N                : in  std_logic                      := 'X';
            NINIT_DONE                 : in  std_logic                      := 'X'
        );
    end component;

    constant VSEC_BASE_ADDRESS : integer := 16#D00#;
    constant PCIE_EPS_INST     : natural := tsel(ENDPOINT_MODE = 0,PCIE_CONS,2*PCIE_CONS);

    signal pcie_reset_status_n      : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_reset_status        : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_rst_local           : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_hip_clk             : std_logic_vector(PCIE_CONS-1 downto 0);
    signal pcie_init_done_n         : std_logic_vector(PCIE_CONS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_EPS_INST-1 downto 0)(RESET_WIDTH+1-1 downto 0);

    signal pcie_avst_down_data      : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_down_hdr       : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS*128-1 downto 0);
    signal pcie_avst_down_prefix    : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS*32-1 downto 0);
    signal pcie_avst_down_sop       : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_eop       : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_empty     : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_bar_range : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_valid     : slv_array_t(PCIE_EPS_INST-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_ready     : std_logic_vector(PCIE_EPS_INST-1 downto 0) := (others => '1');
    signal pcie_avst_up_data        : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_up_hdr         : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS*128-1 downto 0);
    signal pcie_avst_up_prefix      : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS*32-1 downto 0);
    signal pcie_avst_up_sop         : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_eop         : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_error       : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_valid       : slv_array_t(PCIE_EPS_INST-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_ready       : std_logic_vector(PCIE_EPS_INST-1 downto 0);

    signal pcie_link_up_comb        : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_link_up_reg         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cfg_func            : slv_array_t(PCIE_EPS_INST-1 downto 0)(3-1 downto 0);
    signal pcie_cfg_addr            : slv_array_t(PCIE_EPS_INST-1 downto 0)(5-1 downto 0);
    signal pcie_cfg_data            : slv_array_t(PCIE_EPS_INST-1 downto 0)(16-1 downto 0);
    signal pcie_cfg_data_reg        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(16-1 downto 0);
    signal pcie_cfg_pf0_sel         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg0_sel        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg2_sel        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg21_sel       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg0_en         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg2_en         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cfg_reg21_en        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cii_hdr_poisoned    : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_cii_override_en     : std_logic_vector(PCIE_EPS_INST-1 downto 0) := (others => '0');
    signal pcie_cii_hdr_first_be    : slv_array_t(PCIE_EPS_INST-1 downto 0)(3 downto 0);
    signal pcie_cii_dout            : slv_array_t(PCIE_EPS_INST-1 downto 0)(31 downto 0);
    signal pcie_cii_halt            : std_logic_vector(PCIE_EPS_INST-1 downto 0) := (others => '0');
    signal pcie_cii_req             : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_cii_addr            : slv_array_t(PCIE_EPS_INST-1 downto 0)(9 downto 0);
    signal pcie_cii_wr              : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_cii_override_din    : slv_array_t(PCIE_EPS_INST-1 downto 0)(31 downto 0) := (others => (others => '0'));

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_function         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    --==============================================================================================
    -- Other debug signals
    --==============================================================================================
    signal dbg_credits_ph       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal dbg_credits_nph      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal dbg_credits_pd       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(15 downto 0);
    signal dbg_credits_npd      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(15 downto 0);

    signal dbg_credits_ph_vld   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_credits_nph_vld  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_credits_pd_vld   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_credits_npd_vld  : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_dbg_credits     : slv_array_t(PCIE_EPS_INST-1 downto 0)(15 downto 0);
    signal pcie_dbg_credits_sel : slv_array_t(PCIE_EPS_INST-1 downto 0)( 2 downto 0);

    signal dbg_avst_up_src_rdy   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_avst_up_dst_rdy   : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_avst_down_src_rdy : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal dbg_avst_down_dst_rdy : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

begin

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_core_g : for i in 0 to PCIE_CONS-1 generate
        pcie_core_1x16_g : if ENDPOINT_MODE = 0 generate
            pcie_core_i : component ptile_pcie_1x16
            port map (
                p0_rx_st_ready_i             => pcie_avst_down_ready(i),                             --          p0_rx_st.ready
                p0_rx_st_sop_o               => pcie_avst_down_sop(i),                               --                  .startofpacket
                p0_rx_st_eop_o               => pcie_avst_down_eop(i),                               --                  .endofpacket
                p0_rx_st_data_o              => pcie_avst_down_data(i),                              --                  .data
                p0_rx_st_valid_o             => pcie_avst_down_valid(i),                             --                  .valid
                p0_rx_st_empty_o             => pcie_avst_down_empty(i),                             --                  .empty
                p0_rx_st_hdr_o               => pcie_avst_down_hdr(i),                               --     p0_rx_st_misc.rx_st_hdr
                p0_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i),                            --                  .rx_st_tlp_prfx
                p0_rx_st_bar_range_o         => pcie_avst_down_bar_range(i),                         --                  .rx_st_bar_range
                p0_rx_st_tlp_abort_o         => open,                                                --                  .rx_st_tlp_abort
                p0_rx_par_err_o              => open,                                                --                  .rx_par_err
                p0_tx_st_sop_i               => pcie_avst_up_sop(i),                                 --          p0_tx_st.startofpacket
                p0_tx_st_eop_i               => pcie_avst_up_eop(i),                                 --                  .endofpacket
                p0_tx_st_data_i              => pcie_avst_up_data(i),                                --                  .data
                p0_tx_st_valid_i             => pcie_avst_up_valid(i),                               --                  .valid
                p0_tx_st_err_i               => pcie_avst_up_error(i),                               --                  .error
                p0_tx_st_ready_o             => pcie_avst_up_ready(i),                               --                  .ready
                p0_tx_st_hdr_i               => pcie_avst_up_hdr(i),                                 --     p0_tx_st_misc.tx_st_hdr
                p0_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i),                              --                  .tx_st_tlp_prfx
                p0_tx_par_err_o              => open,                                                --                  .tx_par_err
                p0_tx_cdts_limit_o           => pcie_dbg_credits(i*2),                               --        p0_tx_cred.tx_cdts_type
                p0_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2),                           --                  .tx_data_cdts_consumed
                p0_tl_cfg_func_o             => pcie_cfg_func(i),                                    --      p0_config_tl.tl_cfg_func
                p0_tl_cfg_add_o              => pcie_cfg_addr(i),                                    --                  .tl_cfg_add
                p0_tl_cfg_ctl_o              => pcie_cfg_data(i),                                    --                  .tl_cfg_ctl
                p0_dl_timer_update_o         => open,                                                --                  .dl_timer_update
                p0_reset_status_n            => pcie_reset_status_n(i),                              -- p0_reset_status_n.reset_n
                p0_pin_perst_n               => open,                                                --      p0_pin_perst.pin_perst
                p0_link_up_o                 => pcie_link_up_comb(i),                                --     p0_power_mgnt.link_up
                p0_dl_up_o                   => open,                                                --                  .dl_up
                p0_surprise_down_err_o       => open,                                                --                  .surprise_down_err
                p0_pm_state_o                => open,                                                --                  .pm_state
                p0_ltssm_state_o             => open,                                                --                  .ltssmstate
                p0_pm_dstate_o               => open,                                                --                  .pm_dstate
                p0_apps_pm_xmt_pme_i         => (others => '0'),                                     --                  .apps_pm_xmt_pme
                p0_app_req_retry_en_i        => (others => '0'),                                     --                  .app_req_retry_en
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i),                            --            p0_cii.hdr_poisoned
                p0_cii_override_en_i         => pcie_cii_override_en(i),                             --                  .override_en
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i),                            --                  .hdr_first_be
                p0_cii_dout_o                => pcie_cii_dout(i),                                    --                  .dout
                p0_cii_halt_i                => pcie_cii_halt(i),                                    --                  .halt
                p0_cii_req_o                 => pcie_cii_req(i),                                     --                  .req
                p0_cii_addr_o                => pcie_cii_addr(i),                                    --                  .addr
                p0_cii_wr_o                  => pcie_cii_wr(i),                                      --                  .write
                p0_cii_override_din_i        => pcie_cii_override_din(i),                            --                  .override_din
                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),                           --        hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),                           --                  .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),                           --                  .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),                           --                  .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),                           --                  .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),                           --                  .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),                           --                  .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),                           --                  .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),                           --                  .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),                           --                  .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),                          --                  .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),                          --                  .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),                          --                  .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),                          --                  .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),                          --                  .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),                          --                  .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),                           --                  .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),                           --                  .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),                           --                  .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),                           --                  .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),                           --                  .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),                           --                  .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),                           --                  .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),                           --                  .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),                           --                  .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),                           --                  .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),                          --                  .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),                          --                  .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),                          --                  .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),                          --                  .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),                          --                  .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),                          --                  .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),                           --                  .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),                           --                  .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),                           --                  .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),                           --                  .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),                           --                  .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),                           --                  .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),                           --                  .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),                           --                  .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),                           --                  .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),                           --                  .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),                          --                  .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),                          --                  .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),                          --                  .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),                          --                  .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),                          --                  .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),                          --                  .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),                           --                  .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),                           --                  .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),                           --                  .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),                           --                  .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),                           --                  .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),                           --                  .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),                           --                  .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),                           --                  .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),                           --                  .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),                           --                  .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),                          --                  .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),                          --                  .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),                          --                  .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),                          --                  .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),                          --                  .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15),                          --                  .tx_p_out15
                coreclkout_hip               => pcie_hip_clk(i),                                     --    coreclkout_hip.clk
                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),                          --           refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),                        --           refclk1.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),                                    --         pin_perst.pin_perst
                ninit_done                   => pcie_init_done_n(i)                                  --        ninit_done.ninit_done
            );
            pcie_clk(i) <= pcie_hip_clk(i);
            init_done_g : if (PCIE_ENDPOINTS > i) generate
                pcie_init_done_n(i) <= INIT_DONE_N;
            else generate
                pcie_init_done_n(i) <= '1';
            end generate;
        end generate;

        pcie_core_2x8_g : if ENDPOINT_MODE = 1 generate
            pcie_core_i : component ptile_pcie_2x8
            port map (
                p0_rx_st_ready_i             => pcie_avst_down_ready(i*2),                           --          p0_rx_st.ready
                p0_rx_st_sop_o               => pcie_avst_down_sop(i*2),                             --                  .startofpacket
                p0_rx_st_eop_o               => pcie_avst_down_eop(i*2),                             --                  .endofpacket
                p0_rx_st_data_o              => pcie_avst_down_data(i*2),                            --                  .data
                p0_rx_st_valid_o             => pcie_avst_down_valid(i*2),                           --                  .valid
                p0_rx_st_empty_o             => pcie_avst_down_empty(i*2),                           --                  .empty
                p0_rx_st_hdr_o               => pcie_avst_down_hdr(i*2),                             --     p0_rx_st_misc.rx_st_hdr
                p0_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i*2),                          --                  .rx_st_tlp_prfx
                p0_rx_st_bar_range_o         => pcie_avst_down_bar_range(i*2),                       --                  .rx_st_bar_range
                p0_rx_st_tlp_abort_o         => open,                                                --                  .rx_st_tlp_abort
                p0_rx_par_err_o              => open,                                                --                  .rx_par_err
                p0_tx_st_sop_i               => pcie_avst_up_sop(i*2),                               --          p0_tx_st.startofpacket
                p0_tx_st_eop_i               => pcie_avst_up_eop(i*2),                               --                  .endofpacket
                p0_tx_st_data_i              => pcie_avst_up_data(i*2),                              --                  .data
                p0_tx_st_valid_i             => pcie_avst_up_valid(i*2),                             --                  .valid
                p0_tx_st_err_i               => pcie_avst_up_error(i*2),                             --                  .error
                p0_tx_st_ready_o             => pcie_avst_up_ready(i*2),                             --                  .ready
                p0_tx_st_hdr_i               => pcie_avst_up_hdr(i*2),                               --     p0_tx_st_misc.tx_st_hdr
                p0_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i*2),                            --                  .tx_st_tlp_prfx
                p0_tx_par_err_o              => open,                                                --                  .tx_par_err
                p0_tx_cdts_limit_o           => pcie_dbg_credits(i*2),                               --        p0_tx_cred.tx_cdts_type
                p0_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2),                           --                  .tx_data_cdts_consumed
                p0_tl_cfg_func_o             => pcie_cfg_func(i*2),                                  --      p0_config_tl.tl_cfg_func
                p0_tl_cfg_add_o              => pcie_cfg_addr(i*2),                                  --                  .tl_cfg_add
                p0_tl_cfg_ctl_o              => pcie_cfg_data(i*2),                                  --                  .tl_cfg_ctl
                p0_dl_timer_update_o         => open,                                                --                  .dl_timer_update
                p0_reset_status_n            => pcie_reset_status_n(i*2),                            -- p0_reset_status_n.reset_n
                p0_pin_perst_n               => open,                                                --      p0_pin_perst.pin_perst
                p0_link_up_o                 => pcie_link_up_comb(i*2),                              --     p0_power_mgnt.link_up
                p0_dl_up_o                   => open,                                                --                  .dl_up
                p0_surprise_down_err_o       => open,                                                --                  .surprise_down_err
                p0_pm_state_o                => open,                                                --                  .pm_state
                p0_ltssm_state_o             => open,                                                --                  .ltssmstate
                p0_pm_dstate_o               => open,                                                --                  .pm_dstate
                p0_apps_pm_xmt_pme_i         => (others => '0'),                                     --                  .apps_pm_xmt_pme
                p0_app_req_retry_en_i        => (others => '0'),                                     --                  .app_req_retry_en
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2),                          --            p0_cii.hdr_poisoned
                p0_cii_override_en_i         => pcie_cii_override_en(i*2),                           --                  .override_en
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2),                          --                  .hdr_first_be
                p0_cii_dout_o                => pcie_cii_dout(i*2),                                  --                  .dout
                p0_cii_halt_i                => pcie_cii_halt(i*2),                                  --                  .halt
                p0_cii_req_o                 => pcie_cii_req(i*2),                                   --                  .req
                p0_cii_addr_o                => pcie_cii_addr(i*2),                                  --                  .addr
                p0_cii_wr_o                  => pcie_cii_wr(i*2),                                    --                  .write
                p0_cii_override_din_i        => pcie_cii_override_din(i*2),                          --                  .override_din

                p1_rx_st_ready_i             => pcie_avst_down_ready(i*2+1),                           --          p0_rx_st.ready
                p1_rx_st_sop_o               => pcie_avst_down_sop(i*2+1),                             --                  .startofpacket
                p1_rx_st_eop_o               => pcie_avst_down_eop(i*2+1),                             --                  .endofpacket
                p1_rx_st_data_o              => pcie_avst_down_data(i*2+1),                            --                  .data
                p1_rx_st_valid_o             => pcie_avst_down_valid(i*2+1),                           --                  .valid
                p1_rx_st_empty_o             => pcie_avst_down_empty(i*2+1),                           --                  .empty
                p1_rx_st_hdr_o               => pcie_avst_down_hdr(i*2+1),                             --     p0_rx_st_misc.rx_st_hdr
                p1_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i*2+1),                          --                  .rx_st_tlp_prfx
                p1_rx_st_bar_range_o         => pcie_avst_down_bar_range(i*2+1),                       --                  .rx_st_bar_range
                p1_rx_st_tlp_abort_o         => open,                                                  --                  .rx_st_tlp_abort
                p1_rx_par_err_o              => open,                                                  --                  .rx_par_err
                p1_tx_st_sop_i               => pcie_avst_up_sop(i*2+1),                               --          p0_tx_st.startofpacket
                p1_tx_st_eop_i               => pcie_avst_up_eop(i*2+1),                               --                  .endofpacket
                p1_tx_st_data_i              => pcie_avst_up_data(i*2+1),                              --                  .data
                p1_tx_st_valid_i             => pcie_avst_up_valid(i*2+1),                             --                  .valid
                p1_tx_st_err_i               => pcie_avst_up_error(i*2+1),                             --                  .error
                p1_tx_st_ready_o             => pcie_avst_up_ready(i*2+1),                             --                  .ready
                p1_tx_st_hdr_i               => pcie_avst_up_hdr(i*2+1),                               --     p0_tx_st_misc.tx_st_hdr
                p1_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i*2+1),                            --                  .tx_st_tlp_prfx
                p1_tx_par_err_o              => open,                                                  --                  .tx_par_err
                p1_tx_cdts_limit_o           => pcie_dbg_credits(i*2+1),                               --        p0_tx_cred.tx_cdts_type
                p1_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2+1),                           --                  .tx_data_cdts_consumed
                p1_tl_cfg_func_o             => pcie_cfg_func(i*2+1),                                  --      p0_config_tl.tl_cfg_func
                p1_tl_cfg_add_o              => pcie_cfg_addr(i*2+1),                                  --                  .tl_cfg_add
                p1_tl_cfg_ctl_o              => pcie_cfg_data(i*2+1),                                  --                  .tl_cfg_ctl
                p1_dl_timer_update_o         => open,                                                  --                  .dl_timer_update
                p1_reset_status_n            => pcie_reset_status_n(i*2+1),                            -- p0_reset_status_n.reset_n
                p1_pin_perst_n               => open,                                                  --      p0_pin_perst.pin_perst
                p1_link_up_o                 => pcie_link_up_comb(i*2+1),                              --     p0_power_mgnt.link_up
                p1_dl_up_o                   => open,                                                  --                  .dl_up
                p1_surprise_down_err_o       => open,                                                  --                  .surprise_down_err
                p1_pm_state_o                => open,                                                  --                  .pm_state
                p1_ltssm_state_o             => open,                                                  --                  .ltssmstate
                p1_pm_dstate_o               => open,                                                  --                  .pm_dstate
                p1_apps_pm_xmt_pme_i         => (others => '0'),                                       --                  .apps_pm_xmt_pme
                p1_app_req_retry_en_i        => (others => '0'),                                       --                  .app_req_retry_en
                p1_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2+1),                          --            p0_cii.hdr_poisoned
                p1_cii_override_en_i         => pcie_cii_override_en(i*2+1),                           --                  .override_en
                p1_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2+1),                          --                  .hdr_first_be
                p1_cii_dout_o                => pcie_cii_dout(i*2+1),                                  --                  .dout
                p1_cii_halt_i                => pcie_cii_halt(i*2+1),                                  --                  .halt
                p1_cii_req_o                 => pcie_cii_req(i*2+1),                                   --                  .req
                p1_cii_addr_o                => pcie_cii_addr(i*2+1),                                  --                  .addr
                p1_cii_wr_o                  => pcie_cii_wr(i*2+1),                                    --                  .write
                p1_cii_override_din_i        => pcie_cii_override_din(i*2+1),                          --                  .override_din

                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),        --        hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),        --                  .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),        --                  .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),        --                  .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),        --                  .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),        --                  .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),        --                  .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),        --                  .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),        --                  .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),        --                  .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),       --                  .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),       --                  .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),       --                  .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),       --                  .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),       --                  .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),       --                  .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),        --                  .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),        --                  .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),        --                  .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),        --                  .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),        --                  .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),        --                  .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),        --                  .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),        --                  .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),        --                  .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),        --                  .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),       --                  .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),       --                  .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),       --                  .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),       --                  .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),       --                  .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),       --                  .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),        --                  .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),        --                  .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),        --                  .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),        --                  .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),        --                  .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),        --                  .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),        --                  .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),        --                  .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),        --                  .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),        --                  .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),       --                  .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),       --                  .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),       --                  .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),       --                  .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),       --                  .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),       --                  .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),        --                  .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),        --                  .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),        --                  .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),        --                  .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),        --                  .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),        --                  .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),        --                  .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),        --                  .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),        --                  .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),        --                  .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),       --                  .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),       --                  .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),       --                  .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),       --                  .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),       --                  .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15),       --                  .tx_p_out15
                coreclkout_hip               => pcie_hip_clk(i),                  --    coreclkout_hip.clk
                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),       --           refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),     --           refclk1.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),                 --         pin_perst.pin_perst
                ninit_done                   => pcie_init_done_n(i)               --        ninit_done.ninit_done
            );
            pcie_clk(i*2)   <= pcie_hip_clk(i);
            pcie_clk(i*2+1) <= pcie_hip_clk(i);
            init_done_g : if (PCIE_ENDPOINTS > i*2) generate
                pcie_init_done_n(i) <= INIT_DONE_N;
            else generate
                pcie_init_done_n(i) <= '1';
            end generate;
        end generate;
    end generate;

    pcie_adapter_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        -- TODO insert pcie function to HDR

        pcie_adapter_i : entity work.PCIE_ADAPTER
        generic map (
            CQ_MFB_REGIONS     => CQ_MFB_REGIONS,
            CQ_MFB_REGION_SIZE => CQ_MFB_REGION_SIZE,
            CQ_MFB_BLOCK_SIZE  => CQ_MFB_BLOCK_SIZE,
            CQ_MFB_ITEM_WIDTH  => CQ_MFB_ITEM_WIDTH,
            RC_MFB_REGIONS     => RC_MFB_REGIONS,
            RC_MFB_REGION_SIZE => RC_MFB_REGION_SIZE,
            RC_MFB_BLOCK_SIZE  => RC_MFB_BLOCK_SIZE,
            RC_MFB_ITEM_WIDTH  => RC_MFB_ITEM_WIDTH,
            CC_MFB_REGIONS     => CC_MFB_REGIONS,
            CC_MFB_REGION_SIZE => CC_MFB_REGION_SIZE,
            CC_MFB_BLOCK_SIZE  => CC_MFB_BLOCK_SIZE,
            CC_MFB_ITEM_WIDTH  => CC_MFB_ITEM_WIDTH,
            RQ_MFB_REGIONS     => RQ_MFB_REGIONS,
            RQ_MFB_REGION_SIZE => RQ_MFB_REGION_SIZE,
            RQ_MFB_BLOCK_SIZE  => RQ_MFB_BLOCK_SIZE,
            RQ_MFB_ITEM_WIDTH  => RQ_MFB_ITEM_WIDTH,
            ENDPOINT_TYPE      => "P_TILE",
            DEVICE             => DEVICE,
            AXI_CQUSER_WIDTH   => 183,
            AXI_CCUSER_WIDTH   => 81,
            AXI_RQUSER_WIDTH   => 137,
            AXI_RCUSER_WIDTH   => 161,
            AXI_STRADDLING     => false
        )
        port map (
            PCIE_CLK            => pcie_clk(i),
            PCIE_RESET          => pcie_rst(i)(0),

            AVST_DOWN_DATA      => pcie_avst_down_data(i),
            AVST_DOWN_HDR       => pcie_avst_down_hdr(i),
            AVST_DOWN_PREFIX    => pcie_avst_down_prefix(i),
            AVST_DOWN_SOP       => pcie_avst_down_sop(i),
            AVST_DOWN_EOP       => pcie_avst_down_eop(i),
            AVST_DOWN_EMPTY     => pcie_avst_down_empty(i),
            AVST_DOWN_BAR_RANGE => pcie_avst_down_bar_range(i),
            AVST_DOWN_VALID     => pcie_avst_down_valid(i),
            AVST_DOWN_READY     => pcie_avst_down_ready(i),

            AVST_UP_DATA        => pcie_avst_up_data(i),
            AVST_UP_HDR         => pcie_avst_up_hdr(i),
            AVST_UP_PREFIX      => pcie_avst_up_prefix(i),
            AVST_UP_SOP         => pcie_avst_up_sop(i),
            AVST_UP_EOP         => pcie_avst_up_eop(i),
            AVST_UP_ERROR       => pcie_avst_up_error(i),
            AVST_UP_VALID       => pcie_avst_up_valid(i),
            AVST_UP_READY       => pcie_avst_up_ready(i),

            CRDT_DOWN_INIT_DONE => '0',
            CRDT_DOWN_UPDATE    => open,
            CRDT_DOWN_CNT_PH    => open,
            CRDT_DOWN_CNT_NPH   => open,
            CRDT_DOWN_CNT_CPLH  => open,
            CRDT_DOWN_CNT_PD    => open,
            CRDT_DOWN_CNT_NPD   => open,
            CRDT_DOWN_CNT_CPLD  => open,

            CRDT_UP_INIT_DONE   => '0',
            CRDT_UP_UPDATE      => (others => '0'),
            CRDT_UP_CNT_PH      => (others => '0'),
            CRDT_UP_CNT_NPH     => (others => '0'),
            CRDT_UP_CNT_CPLH    => (others => '0'),
            CRDT_UP_CNT_PD      => (others => '0'),
            CRDT_UP_CNT_NPD     => (others => '0'),
            CRDT_UP_CNT_CPLD    => (others => '0'),

            CQ_AXI_DATA         => (others => '0'),
            CQ_AXI_USER         => (others => '0'),
            CQ_AXI_LAST         => '0',
            CQ_AXI_KEEP         => (others => '0'),
            CQ_AXI_VALID        => '0',
            CQ_AXI_READY        => open,

            RC_AXI_DATA         => (others => '0'),
            RC_AXI_USER         => (others => '0'),
            RC_AXI_LAST         => '0',
            RC_AXI_KEEP         => (others => '0'),
            RC_AXI_VALID        => '0',
            RC_AXI_READY        => open,

            CC_AXI_DATA         => open,
            CC_AXI_USER         => open,
            CC_AXI_LAST         => open,
            CC_AXI_KEEP         => open,
            CC_AXI_VALID        => open,
            CC_AXI_READY        => '0',

            RQ_AXI_DATA         => open,
            RQ_AXI_USER         => open,
            RQ_AXI_LAST         => open,
            RQ_AXI_KEEP         => open,
            RQ_AXI_VALID        => open,
            RQ_AXI_READY        => '0',

            CQ_MFB_DATA         => CQ_MFB_DATA(i),
            CQ_MFB_META         => CQ_MFB_META(i),
            CQ_MFB_SOF          => CQ_MFB_SOF(i),
            CQ_MFB_EOF          => CQ_MFB_EOF(i),
            CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS(i),
            CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS(i),
            CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY(i),
            CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY(i),

            RC_MFB_DATA         => RC_MFB_DATA(i),
            RC_MFB_META         => RC_MFB_META(i),
            RC_MFB_SOF          => RC_MFB_SOF(i),
            RC_MFB_EOF          => RC_MFB_EOF(i),
            RC_MFB_SOF_POS      => RC_MFB_SOF_POS(i),
            RC_MFB_EOF_POS      => RC_MFB_EOF_POS(i),
            RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY(i),
            RC_MFB_DST_RDY      => RC_MFB_DST_RDY(i),

            CC_MFB_DATA         => CC_MFB_DATA(i),
            CC_MFB_META         => CC_MFB_META(i),
            CC_MFB_SOF          => CC_MFB_SOF(i),
            CC_MFB_EOF          => CC_MFB_EOF(i),
            CC_MFB_SOF_POS      => CC_MFB_SOF_POS(i),
            CC_MFB_EOF_POS      => CC_MFB_EOF_POS(i),
            CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY(i),
            CC_MFB_DST_RDY      => CC_MFB_DST_RDY(i),

            RQ_MFB_DATA         => RQ_MFB_DATA(i),
            RQ_MFB_META         => RQ_MFB_META(i),
            RQ_MFB_SOF          => RQ_MFB_SOF(i),
            RQ_MFB_EOF          => RQ_MFB_EOF(i),
            RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS(i),
            RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS(i),
            RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY(i),
            RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY(i)
        );
    end generate;

    -- user PCI reset
    pcie_reset_status <= not pcie_reset_status_n;

    pcie_rst_g : for i in 0 to PCIE_EPS_INST-1 generate
        pcie_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RESET_WIDTH+1
        )
        port map (
            CLK       => pcie_clk(i),
            ASYNC_RST => pcie_reset_status(i),
            OUT_RST   => pcie_rst(i)
        );

        pcie_rst_local(i) <= pcie_rst(i)(0);
    end generate;

    pcie_clk_rst_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        PCIE_USER_CLK(i)   <= pcie_clk(i);
        PCIE_USER_RESET(i) <= pcie_rst(i)(RESET_WIDTH+1-1 downto 1);
    end generate;

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================

    pcie_cfg_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                pcie_link_up_reg(i) <= pcie_link_up_comb(i);
                PCIE_LINK_UP(i)     <= pcie_link_up_reg(i);
            end if;
        end process;

        pcie_cfg_pf0_sel(i)   <= '1' when (unsigned(pcie_cfg_func(i)) = 0) else '0';
        pcie_cfg_reg0_sel(i)  <= '1' when (unsigned(pcie_cfg_addr(i)) = 0) else '0';
        pcie_cfg_reg2_sel(i)  <= '1' when (unsigned(pcie_cfg_addr(i)) = 2) else '0';
        pcie_cfg_reg21_sel(i) <= '1' when (unsigned(pcie_cfg_addr(i)) = 21) else '0';

        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                pcie_cfg_reg0_en(i)  <= pcie_cfg_reg0_sel(i) and pcie_cfg_pf0_sel(i);
                pcie_cfg_reg2_en(i)  <= pcie_cfg_reg2_sel(i) and pcie_cfg_pf0_sel(i);
                pcie_cfg_reg21_en(i) <= pcie_cfg_reg21_sel(i) and pcie_cfg_pf0_sel(i);
                pcie_cfg_data_reg(i) <= pcie_cfg_data(i);
            end if;
        end process;

        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                if (pcie_cfg_reg0_en(i) = '1') then
                    PCIE_MPS(i)        <= pcie_cfg_data_reg(i)(2 downto 0);
                    PCIE_MRRS(i)       <= pcie_cfg_data_reg(i)(5 downto 3);
                    PCIE_EXT_TAG_EN(i) <= pcie_cfg_data_reg(i)(6);
                end if;
                if (pcie_cfg_reg2_en(i) = '1') then
                    PCIE_RCB_SIZE(i) <= pcie_cfg_data_reg(i)(14);
                end if;
                if (pcie_cfg_reg21_en(i) = '1') then
                    PCIE_10B_TAG_REQ_EN(i) <= pcie_cfg_data_reg(i)(14);
                end if;
            end if;
        end process;
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        constant DT_EN : boolean := true;
    begin
        cii2cfg_ext_i: entity work.PCIE_CII2CFG_EXT
        port map (
            CLK                    => pcie_clk(i),
            RESET                  => pcie_rst(i)(0),

            PCIE_CII_HDR_POISONED  => pcie_cii_hdr_poisoned(i),
            PCIE_CII_OVERRIDE_EN   => pcie_cii_override_en(i),
            PCIE_CII_HDR_FIRST_BE  => pcie_cii_hdr_first_be(i),
            PCIE_CII_DOUT          => pcie_cii_dout(i),
            PCIE_CII_HALT          => pcie_cii_halt(i),
            PCIE_CII_REQ           => pcie_cii_req(i),
            PCIE_CII_ADDR          => pcie_cii_addr(i),
            PCIE_CII_WR            => pcie_cii_wr(i),
            PCIE_CII_OVERRIDE_DIN  => pcie_cii_override_din(i),

            CFG_EXT_READ           => cfg_ext_read(i),
            CFG_EXT_WRITE          => cfg_ext_write(i),
            CFG_EXT_REGISTER       => cfg_ext_register(i),
            CFG_EXT_FUNCTION       => cfg_ext_function(i),
            CFG_EXT_WRITE_DATA     => cfg_ext_write_data(i),
            CFG_EXT_WRITE_BE       => cfg_ext_write_be(i),
            CFG_EXT_READ_DATA      => cfg_ext_read_data(i),
            CFG_EXT_READ_DV        => cfg_ext_read_dv(i)
        );

        -- Device Tree ROM
        pci_ext_cap_i: entity work.PCI_EXT_CAP
        generic map (
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => dt_en,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => 16#000#,
            CARD_ID_WIDTH          => CARD_ID_WIDTH,
            CFG_EXT_READ_DV_HOTFIX => false
        )
        port map (
            CLK                    => pcie_clk(i),
            CARD_ID                => CARD_ID(i),
            CFG_EXT_READ           => cfg_ext_read(i),
            CFG_EXT_WRITE          => cfg_ext_write(i),
            CFG_EXT_REGISTER       => cfg_ext_register(i),
            CFG_EXT_FUNCTION       => cfg_ext_function(i),
            CFG_EXT_WRITE_DATA     => cfg_ext_write_data(i),
            CFG_EXT_WRITE_BE       => cfg_ext_write_be(i),
            CFG_EXT_READ_DATA      => cfg_ext_read_data(i),
            CFG_EXT_READ_DV        => cfg_ext_read_dv(i)
        );
    end generate;

    -- =========================================================================
    --  DEBUG logic
    -- =========================================================================

    pcie_endpoints_dbg_g : for pe in 0 to PCIE_ENDPOINTS-1 generate
        dbg_avst_up_src_rdy(pe)   <= (or pcie_avst_up_valid(pe));
        dbg_avst_up_dst_rdy(pe)   <= pcie_avst_up_ready(pe);
        dbg_avst_down_src_rdy(pe) <= (or pcie_avst_down_valid(pe));
        dbg_avst_down_dst_rdy(pe) <= pcie_avst_down_ready(pe);

        dbg_credits_ph (pe) <= pcie_dbg_credits(pe)(11 downto 0); -- "When the traffic type is header credit, only the LSB 12 bits are valid" - Intel doc
        dbg_credits_nph(pe) <= pcie_dbg_credits(pe)(11 downto 0); -- "When the traffic type is header credit, only the LSB 12 bits are valid" - Intel doc
        dbg_credits_pd (pe) <= pcie_dbg_credits(pe);
        dbg_credits_npd(pe) <= pcie_dbg_credits(pe);

        dbg_credits_ph_vld (pe) <= '1' when (pcie_dbg_credits_sel(pe) = "000") else '0'; --     Posted header credit limit
        dbg_credits_nph_vld(pe) <= '1' when (pcie_dbg_credits_sel(pe) = "001") else '0'; -- Non-Posted header credit limit
        dbg_credits_pd_vld (pe) <= '1' when (pcie_dbg_credits_sel(pe) = "100") else '0'; --     Posted data   credit limit
        dbg_credits_npd_vld(pe) <= '1' when (pcie_dbg_credits_sel(pe) = "101") else '0'; -- Non-Posted data   credit limit
    end generate;

    debug_i : entity work.PCIE_CORE_DEBUG
    generic map (
        PCIE_ENDPOINTS => PCIE_ENDPOINTS,
        DBG_CRDT_PH_W  => 12,
        DBG_CRDT_NPH_W => 12,
        DBG_CRDT_PD_W  => 16,
        DBG_CRDT_NPD_W => 16,
        DBG_ENABLE     => PCIE_CORE_DEBUG_ENABLE,
        DEVICE         => DEVICE
    )
    port map (
        PCIE_CLK            => pcie_clk(PCIE_ENDPOINTS-1 downto 0),
        PCIE_RESET          => pcie_rst_local(PCIE_ENDPOINTS-1 downto 0),

        DBG_UP_SRC_RDY      => dbg_avst_up_src_rdy,
        DBG_UP_DST_RDY      => dbg_avst_up_dst_rdy,
        DBG_DW_SRC_RDY      => dbg_avst_down_src_rdy,
        DBG_DW_DST_RDY      => dbg_avst_down_dst_rdy,

        DBG_CREDITS_PH      => dbg_credits_ph,
        DBG_CREDITS_NPH     => dbg_credits_nph,
        DBG_CREDITS_PD      => dbg_credits_pd,
        DBG_CREDITS_NPD     => dbg_credits_npd,

        DBG_CREDITS_PH_VLD  => dbg_credits_ph_vld,
        DBG_CREDITS_NPH_VLD => dbg_credits_nph_vld,
        DBG_CREDITS_PD_VLD  => dbg_credits_pd_vld,
        DBG_CREDITS_NPD_VLD => dbg_credits_npd_vld,

        MI_CLK              => MI_CLK,
        MI_RESET            => MI_RESET,
        MI_DWR              => MI_DWR,
        MI_ADDR             => MI_ADDR,
        MI_BE               => MI_BE,
        MI_RD               => MI_RD,
        MI_WR               => MI_WR,
        MI_ARDY             => MI_ARDY,
        MI_DRD              => MI_DRD,
        MI_DRDY             => MI_DRDY
    );

end architecture;
