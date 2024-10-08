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
-- It contains a number of debug components.
-- Streaming Debug Probes monitor SRC and DST RDY signals and and Event Counters monitor the number of available PCIe credits for each Hard IP core.
-- They are controlled over the MI interface.
--
-- **MI address space**
--
-- .. Warning::
--
--     For the 1x16 variant, each Streaming Debug Master has two connected Slave probes, because the IP core has two AVST buses (with a common DST RDY).
--     In that case, the address range in the table above for the Streaming Debug Master is doubled.
--     That means all other ranges are shifted by the new offset (2 x 0x40).
--
-- +----------------+----------------+------------------------------------------------------------------------------------------------+
-- | Hard IP | Component                                                                                            | Address range   |
-- +=========+======================================================================================================+=================+
-- |         | Streaming Debug (Master with one or two Probe(s))                                                    |   0x00 - 0x3F   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x40 - 0x4F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x50 - 0x5F   |
-- +         | Event Counter(s) - signal: PCIe credits of Posted HEADERS     +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x60 - 0x6F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x70 - 0x7F   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x80 - 0x8F   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x90 - 0x9F   |
-- +         | Event Counter(s) - signal: PCIe credits of Posted DATA        +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0xA0 - 0xAF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0xB0 - 0xBF   |
-- +    0    +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0xC0 - 0xCF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0xD0 - 0xDF   |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted HEADERS +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0xE0 - 0xEF   |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0xF0 - 0xFF   |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x100 - 0x10F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x110 - 0x11F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted DATA    +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x120 - 0x12F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x130 - 0x13F |
-- +---------+------------------------------------------------------------------------------------------------------+-----------------+
-- |         | Streaming Debug (Master with one or two Probe(s))                                                    |   0x140 - 0x17F |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x180 - 0x18F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x190 - 0x19F |
-- +         | Event Counter(s) - signal: PCIe credits of Posted HEADERS     +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x1A0 - 0x1AF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x1B0 - 0x1BF |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x1C0 - 0x1CF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x1D0 - 0x1DF |
-- +         | Event Counter(s) - signal: PCIe credits of Posted DATA        +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x1E0 - 0x1EF |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x1F0 - 0x1FF |
-- +    1    +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x200 - 0x20F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x210 - 0x21F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted HEADERS +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x220 - 0x22F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-255  |   0x230 - 0x23F |
-- +         +------------------------------------------------------------------------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 0-7      |   0x240 - 0x24F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 8-31     |   0x250 - 0x25F |
-- +         | Event Counter(s) - signal: PCIe credits of Non-Posted DATA    +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 32-127   |   0x260 - 0x26F |
-- +         |                                                               +--------------------------------------+-----------------+
-- |         |                                                               | Monitored range of credits: 128-4095 |   0x270 - 0x27F |
-- +---------+------------------------------------------------------------------------------------------------------+-----------------+
--
architecture PTILE of PCIE_CORE is

    component ptile_pcie_1x16 is
        port (
            p0_rx_st_ready_i             : in  std_logic                      := 'X';             -- ready
            p0_rx_st_sop_o               : out std_logic_vector(1 downto 0);                      -- startofpacket
            p0_rx_st_eop_o               : out std_logic_vector(1 downto 0);                      -- endofpacket
            p0_rx_st_data_o              : out std_logic_vector(511 downto 0);                    -- data
            p0_rx_st_valid_o             : out std_logic_vector(1 downto 0);                      -- valid
            p0_rx_st_empty_o             : out std_logic_vector(5 downto 0);                      -- empty
            p0_rx_st_hdr_o               : out std_logic_vector(255 downto 0);                    -- rx_st_hdr
            p0_rx_st_tlp_prfx_o          : out std_logic_vector(63 downto 0);                     -- rx_st_tlp_prfx
            p0_rx_st_bar_range_o         : out std_logic_vector(5 downto 0);                      -- rx_st_bar_range
            p0_rx_st_tlp_abort_o         : out std_logic_vector(1 downto 0);                      -- rx_st_tlp_abort
            p0_rx_par_err_o              : out std_logic;                                         -- rx_par_err
            p0_tx_st_sop_i               : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- startofpacket
            p0_tx_st_eop_i               : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- endofpacket
            p0_tx_st_data_i              : in  std_logic_vector(511 downto 0) := (others => 'X'); -- data
            p0_tx_st_valid_i             : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- valid
            p0_tx_st_err_i               : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- error
            p0_tx_st_ready_o             : out std_logic;                                         -- ready
            p0_tx_st_hdr_i               : in  std_logic_vector(255 downto 0) := (others => 'X'); -- tx_st_hdr
            p0_tx_st_tlp_prfx_i          : in  std_logic_vector(63 downto 0)  := (others => 'X'); -- tx_st_tlp_prfx
            p0_tx_par_err_o              : out std_logic;                                         -- tx_par_err
            p0_tx_cdts_limit_o           : out std_logic_vector(15 downto 0);                     -- tx_cdts_type
            p0_tx_cdts_limit_tdm_idx_o   : out std_logic_vector(2 downto 0);                      -- tx_data_cdts_consumed
            p0_tl_cfg_func_o             : out std_logic_vector(2 downto 0);                      -- tl_cfg_func
            p0_tl_cfg_add_o              : out std_logic_vector(4 downto 0);                      -- tl_cfg_add
            p0_tl_cfg_ctl_o              : out std_logic_vector(15 downto 0);                     -- tl_cfg_ctl
            p0_dl_timer_update_o         : out std_logic;                                         -- dl_timer_update
            p0_reset_status_n            : out std_logic;                                         -- reset_n
            p0_pin_perst_n               : out std_logic;                                         -- pin_perst
            p0_link_up_o                 : out std_logic;                                         -- link_up
            p0_dl_up_o                   : out std_logic;                                         -- dl_up
            p0_surprise_down_err_o       : out std_logic;                                         -- surprise_down_err
            p0_pm_state_o                : out std_logic_vector(2 downto 0);                      -- pm_state
            p0_ltssm_state_o             : out std_logic_vector(5 downto 0);                      -- ltssmstate
            p0_pm_dstate_o               : out std_logic_vector(31 downto 0);                     -- pm_dstate
            p0_apps_pm_xmt_pme_i         : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- apps_pm_xmt_pme
            p0_app_req_retry_en_i        : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- app_req_retry_en
            p0_cii_hdr_poisoned_o        : out std_logic;                                         -- hdr_poisoned
            p0_cii_override_en_i         : in  std_logic                      := 'X';             -- override_en
            p0_cii_hdr_first_be_o        : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p0_cii_dout_o                : out std_logic_vector(31 downto 0);                     -- dout
            p0_cii_halt_i                : in  std_logic                      := 'X';             -- halt
            p0_cii_req_o                 : out std_logic;                                         -- req
            p0_cii_addr_o                : out std_logic_vector(9 downto 0);                      -- addr
            p0_cii_wr_o                  : out std_logic;                                         -- write
            p0_cii_override_din_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            rx_n_in0                     : in  std_logic                      := 'X';             -- rx_n_in0
            rx_n_in1                     : in  std_logic                      := 'X';             -- rx_n_in1
            rx_n_in2                     : in  std_logic                      := 'X';             -- rx_n_in2
            rx_n_in3                     : in  std_logic                      := 'X';             -- rx_n_in3
            rx_n_in4                     : in  std_logic                      := 'X';             -- rx_n_in4
            rx_n_in5                     : in  std_logic                      := 'X';             -- rx_n_in5
            rx_n_in6                     : in  std_logic                      := 'X';             -- rx_n_in6
            rx_n_in7                     : in  std_logic                      := 'X';             -- rx_n_in7
            rx_n_in8                     : in  std_logic                      := 'X';             -- rx_n_in8
            rx_n_in9                     : in  std_logic                      := 'X';             -- rx_n_in9
            rx_n_in10                    : in  std_logic                      := 'X';             -- rx_n_in10
            rx_n_in11                    : in  std_logic                      := 'X';             -- rx_n_in11
            rx_n_in12                    : in  std_logic                      := 'X';             -- rx_n_in12
            rx_n_in13                    : in  std_logic                      := 'X';             -- rx_n_in13
            rx_n_in14                    : in  std_logic                      := 'X';             -- rx_n_in14
            rx_n_in15                    : in  std_logic                      := 'X';             -- rx_n_in15
            rx_p_in0                     : in  std_logic                      := 'X';             -- rx_p_in0
            rx_p_in1                     : in  std_logic                      := 'X';             -- rx_p_in1
            rx_p_in2                     : in  std_logic                      := 'X';             -- rx_p_in2
            rx_p_in3                     : in  std_logic                      := 'X';             -- rx_p_in3
            rx_p_in4                     : in  std_logic                      := 'X';             -- rx_p_in4
            rx_p_in5                     : in  std_logic                      := 'X';             -- rx_p_in5
            rx_p_in6                     : in  std_logic                      := 'X';             -- rx_p_in6
            rx_p_in7                     : in  std_logic                      := 'X';             -- rx_p_in7
            rx_p_in8                     : in  std_logic                      := 'X';             -- rx_p_in8
            rx_p_in9                     : in  std_logic                      := 'X';             -- rx_p_in9
            rx_p_in10                    : in  std_logic                      := 'X';             -- rx_p_in10
            rx_p_in11                    : in  std_logic                      := 'X';             -- rx_p_in11
            rx_p_in12                    : in  std_logic                      := 'X';             -- rx_p_in12
            rx_p_in13                    : in  std_logic                      := 'X';             -- rx_p_in13
            rx_p_in14                    : in  std_logic                      := 'X';             -- rx_p_in14
            rx_p_in15                    : in  std_logic                      := 'X';             -- rx_p_in15
            tx_n_out0                    : out std_logic;                                         -- tx_n_out0
            tx_n_out1                    : out std_logic;                                         -- tx_n_out1
            tx_n_out2                    : out std_logic;                                         -- tx_n_out2
            tx_n_out3                    : out std_logic;                                         -- tx_n_out3
            tx_n_out4                    : out std_logic;                                         -- tx_n_out4
            tx_n_out5                    : out std_logic;                                         -- tx_n_out5
            tx_n_out6                    : out std_logic;                                         -- tx_n_out6
            tx_n_out7                    : out std_logic;                                         -- tx_n_out7
            tx_n_out8                    : out std_logic;                                         -- tx_n_out8
            tx_n_out9                    : out std_logic;                                         -- tx_n_out9
            tx_n_out10                   : out std_logic;                                         -- tx_n_out10
            tx_n_out11                   : out std_logic;                                         -- tx_n_out11
            tx_n_out12                   : out std_logic;                                         -- tx_n_out12
            tx_n_out13                   : out std_logic;                                         -- tx_n_out13
            tx_n_out14                   : out std_logic;                                         -- tx_n_out14
            tx_n_out15                   : out std_logic;                                         -- tx_n_out15
            tx_p_out0                    : out std_logic;                                         -- tx_p_out0
            tx_p_out1                    : out std_logic;                                         -- tx_p_out1
            tx_p_out2                    : out std_logic;                                         -- tx_p_out2
            tx_p_out3                    : out std_logic;                                         -- tx_p_out3
            tx_p_out4                    : out std_logic;                                         -- tx_p_out4
            tx_p_out5                    : out std_logic;                                         -- tx_p_out5
            tx_p_out6                    : out std_logic;                                         -- tx_p_out6
            tx_p_out7                    : out std_logic;                                         -- tx_p_out7
            tx_p_out8                    : out std_logic;                                         -- tx_p_out8
            tx_p_out9                    : out std_logic;                                         -- tx_p_out9
            tx_p_out10                   : out std_logic;                                         -- tx_p_out10
            tx_p_out11                   : out std_logic;                                         -- tx_p_out11
            tx_p_out12                   : out std_logic;                                         -- tx_p_out12
            tx_p_out13                   : out std_logic;                                         -- tx_p_out13
            tx_p_out14                   : out std_logic;                                         -- tx_p_out14
            tx_p_out15                   : out std_logic;                                         -- tx_p_out15
            coreclkout_hip               : out std_logic;                                         -- clk
            refclk0                      : in  std_logic                      := 'X';             -- clk
            refclk1                      : in  std_logic                      := 'X';             -- clk
            pin_perst_n                  : in  std_logic                      := 'X';             -- pin_perst
            ninit_done                   : in  std_logic                      := 'X'              -- ninit_done
        );
    end component ptile_pcie_1x16;

    component ptile_pcie_2x8 is
        port (
            p0_rx_st_ready_i           : in  std_logic                      := 'X';             -- ready
            p0_rx_st_sop_o             : out std_logic_vector(0 downto 0);                      -- startofpacket
            p0_rx_st_eop_o             : out std_logic_vector(0 downto 0);                      -- endofpacket
            p0_rx_st_data_o            : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st_valid_o           : out std_logic_vector(0 downto 0);                      -- valid
            p0_rx_st_empty_o           : out std_logic_vector(2 downto 0);                      -- empty
            p0_rx_st_hdr_o             : out std_logic_vector(127 downto 0);                    -- rx_st_hdr
            p0_rx_st_tlp_prfx_o        : out std_logic_vector(31 downto 0);                     -- rx_st_tlp_prfx
            p0_rx_st_bar_range_o       : out std_logic_vector(2 downto 0);                      -- rx_st_bar_range
            p0_rx_st_tlp_abort_o       : out std_logic_vector(0 downto 0);                      -- rx_st_tlp_abort
            p0_rx_par_err_o            : out std_logic;                                         -- rx_par_err
            p0_tx_st_sop_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- startofpacket
            p0_tx_st_eop_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- endofpacket
            p0_tx_st_data_i            : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st_valid_i           : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- valid
            p0_tx_st_err_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- error
            p0_tx_st_ready_o           : out std_logic;                                         -- ready
            p0_tx_st_hdr_i             : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st_hdr
            p0_tx_st_tlp_prfx_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st_tlp_prfx
            p0_tx_par_err_o            : out std_logic;                                         -- tx_par_err
            p0_tx_cdts_limit_o         : out std_logic_vector(15 downto 0);                     -- tx_cdts_type
            p0_tx_cdts_limit_tdm_idx_o : out std_logic_vector(2 downto 0);                      -- tx_data_cdts_consumed
            p0_tl_cfg_func_o           : out std_logic_vector(2 downto 0);                      -- tl_cfg_func
            p0_tl_cfg_add_o            : out std_logic_vector(4 downto 0);                      -- tl_cfg_add
            p0_tl_cfg_ctl_o            : out std_logic_vector(15 downto 0);                     -- tl_cfg_ctl
            p0_dl_timer_update_o       : out std_logic;                                         -- dl_timer_update
            p1_rx_st_ready_i           : in  std_logic                      := 'X';             -- ready
            p1_rx_st_sop_o             : out std_logic_vector(0 downto 0);                      -- startofpacket
            p1_rx_st_eop_o             : out std_logic_vector(0 downto 0);                      -- endofpacket
            p1_rx_st_data_o            : out std_logic_vector(255 downto 0);                    -- data
            p1_rx_st_valid_o           : out std_logic_vector(0 downto 0);                      -- valid
            p1_rx_st_empty_o           : out std_logic_vector(2 downto 0);                      -- empty
            p1_rx_st_hdr_o             : out std_logic_vector(127 downto 0);                    -- rx_st_hdr
            p1_rx_st_tlp_prfx_o        : out std_logic_vector(31 downto 0);                     -- rx_st_tlp_prfx
            p1_rx_st_bar_range_o       : out std_logic_vector(2 downto 0);                      -- rx_st_bar_range
            p1_rx_st_tlp_abort_o       : out std_logic_vector(0 downto 0);                      -- rx_st_tlp_abort
            p1_rx_par_err_o            : out std_logic;                                         -- rx_par_err
            p1_tx_st_sop_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- startofpacket
            p1_tx_st_eop_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- endofpacket
            p1_tx_st_data_i            : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p1_tx_st_valid_i           : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- valid
            p1_tx_st_err_i             : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- error
            p1_tx_st_ready_o           : out std_logic;                                         -- ready
            p1_tx_st_hdr_i             : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st_hdr
            p1_tx_st_tlp_prfx_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st_tlp_prfx
            p1_tx_par_err_o            : out std_logic;                                         -- tx_par_err
            p1_tx_cdts_limit_o         : out std_logic_vector(15 downto 0);                     -- tx_cdts_type
            p1_tx_cdts_limit_tdm_idx_o : out std_logic_vector(2 downto 0);                      -- tx_data_cdts_consumed
            p1_tl_cfg_func_o           : out std_logic_vector(2 downto 0);                      -- tl_cfg_func
            p1_tl_cfg_add_o            : out std_logic_vector(4 downto 0);                      -- tl_cfg_add
            p1_tl_cfg_ctl_o            : out std_logic_vector(15 downto 0);                     -- tl_cfg_ctl
            p1_dl_timer_update_o       : out std_logic;                                         -- dl_timer_update
            p1_reset_status_n          : out std_logic;                                         -- reset_n
            p1_pin_perst_n             : out std_logic;                                         -- pin_perst
            p1_link_up_o               : out std_logic;                                         -- link_up
            p1_dl_up_o                 : out std_logic;                                         -- dl_up
            p1_surprise_down_err_o     : out std_logic;                                         -- surprise_down_err
            p1_pm_state_o              : out std_logic_vector(2 downto 0);                      -- pm_state
            p1_ltssm_state_o           : out std_logic_vector(5 downto 0);                      -- ltssmstate
            p1_pm_dstate_o             : out std_logic_vector(31 downto 0);                     -- pm_dstate
            p1_apps_pm_xmt_pme_i       : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- apps_pm_xmt_pme
            p1_app_req_retry_en_i      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- app_req_retry_en
            p1_cii_hdr_poisoned_o      : out std_logic;                                         -- hdr_poisoned
            p1_cii_override_en_i       : in  std_logic                      := 'X';             -- override_en
            p1_cii_hdr_first_be_o      : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p1_cii_dout_o              : out std_logic_vector(31 downto 0);                     -- dout
            p1_cii_halt_i              : in  std_logic                      := 'X';             -- halt
            p1_cii_req_o               : out std_logic;                                         -- req
            p1_cii_addr_o              : out std_logic_vector(9 downto 0);                      -- addr
            p1_cii_wr_o                : out std_logic;                                         -- write
            p1_cii_override_din_i      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            p0_reset_status_n          : out std_logic;                                         -- reset_n
            p0_pin_perst_n             : out std_logic;                                         -- pin_perst
            p0_link_up_o               : out std_logic;                                         -- link_up
            p0_dl_up_o                 : out std_logic;                                         -- dl_up
            p0_surprise_down_err_o     : out std_logic;                                         -- surprise_down_err
            p0_pm_state_o              : out std_logic_vector(2 downto 0);                      -- pm_state
            p0_ltssm_state_o           : out std_logic_vector(5 downto 0);                      -- ltssmstate
            p0_pm_dstate_o             : out std_logic_vector(31 downto 0);                     -- pm_dstate
            p0_apps_pm_xmt_pme_i       : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- apps_pm_xmt_pme
            p0_app_req_retry_en_i      : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- app_req_retry_en
            p0_cii_hdr_poisoned_o      : out std_logic;                                         -- hdr_poisoned
            p0_cii_override_en_i       : in  std_logic                      := 'X';             -- override_en
            p0_cii_hdr_first_be_o      : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p0_cii_dout_o              : out std_logic_vector(31 downto 0);                     -- dout
            p0_cii_halt_i              : in  std_logic                      := 'X';             -- halt
            p0_cii_req_o               : out std_logic;                                         -- req
            p0_cii_addr_o              : out std_logic_vector(9 downto 0);                      -- addr
            p0_cii_wr_o                : out std_logic;                                         -- write
            p0_cii_override_din_i      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            rx_n_in0                   : in  std_logic                      := 'X';             -- rx_n_in0
            rx_n_in1                   : in  std_logic                      := 'X';             -- rx_n_in1
            rx_n_in2                   : in  std_logic                      := 'X';             -- rx_n_in2
            rx_n_in3                   : in  std_logic                      := 'X';             -- rx_n_in3
            rx_n_in4                   : in  std_logic                      := 'X';             -- rx_n_in4
            rx_n_in5                   : in  std_logic                      := 'X';             -- rx_n_in5
            rx_n_in6                   : in  std_logic                      := 'X';             -- rx_n_in6
            rx_n_in7                   : in  std_logic                      := 'X';             -- rx_n_in7
            rx_n_in8                   : in  std_logic                      := 'X';             -- rx_n_in8
            rx_n_in9                   : in  std_logic                      := 'X';             -- rx_n_in9
            rx_n_in10                  : in  std_logic                      := 'X';             -- rx_n_in10
            rx_n_in11                  : in  std_logic                      := 'X';             -- rx_n_in11
            rx_n_in12                  : in  std_logic                      := 'X';             -- rx_n_in12
            rx_n_in13                  : in  std_logic                      := 'X';             -- rx_n_in13
            rx_n_in14                  : in  std_logic                      := 'X';             -- rx_n_in14
            rx_n_in15                  : in  std_logic                      := 'X';             -- rx_n_in15
            rx_p_in0                   : in  std_logic                      := 'X';             -- rx_p_in0
            rx_p_in1                   : in  std_logic                      := 'X';             -- rx_p_in1
            rx_p_in2                   : in  std_logic                      := 'X';             -- rx_p_in2
            rx_p_in3                   : in  std_logic                      := 'X';             -- rx_p_in3
            rx_p_in4                   : in  std_logic                      := 'X';             -- rx_p_in4
            rx_p_in5                   : in  std_logic                      := 'X';             -- rx_p_in5
            rx_p_in6                   : in  std_logic                      := 'X';             -- rx_p_in6
            rx_p_in7                   : in  std_logic                      := 'X';             -- rx_p_in7
            rx_p_in8                   : in  std_logic                      := 'X';             -- rx_p_in8
            rx_p_in9                   : in  std_logic                      := 'X';             -- rx_p_in9
            rx_p_in10                  : in  std_logic                      := 'X';             -- rx_p_in10
            rx_p_in11                  : in  std_logic                      := 'X';             -- rx_p_in11
            rx_p_in12                  : in  std_logic                      := 'X';             -- rx_p_in12
            rx_p_in13                  : in  std_logic                      := 'X';             -- rx_p_in13
            rx_p_in14                  : in  std_logic                      := 'X';             -- rx_p_in14
            rx_p_in15                  : in  std_logic                      := 'X';             -- rx_p_in15
            tx_n_out0                  : out std_logic;                                         -- tx_n_out0
            tx_n_out1                  : out std_logic;                                         -- tx_n_out1
            tx_n_out2                  : out std_logic;                                         -- tx_n_out2
            tx_n_out3                  : out std_logic;                                         -- tx_n_out3
            tx_n_out4                  : out std_logic;                                         -- tx_n_out4
            tx_n_out5                  : out std_logic;                                         -- tx_n_out5
            tx_n_out6                  : out std_logic;                                         -- tx_n_out6
            tx_n_out7                  : out std_logic;                                         -- tx_n_out7
            tx_n_out8                  : out std_logic;                                         -- tx_n_out8
            tx_n_out9                  : out std_logic;                                         -- tx_n_out9
            tx_n_out10                 : out std_logic;                                         -- tx_n_out10
            tx_n_out11                 : out std_logic;                                         -- tx_n_out11
            tx_n_out12                 : out std_logic;                                         -- tx_n_out12
            tx_n_out13                 : out std_logic;                                         -- tx_n_out13
            tx_n_out14                 : out std_logic;                                         -- tx_n_out14
            tx_n_out15                 : out std_logic;                                         -- tx_n_out15
            tx_p_out0                  : out std_logic;                                         -- tx_p_out0
            tx_p_out1                  : out std_logic;                                         -- tx_p_out1
            tx_p_out2                  : out std_logic;                                         -- tx_p_out2
            tx_p_out3                  : out std_logic;                                         -- tx_p_out3
            tx_p_out4                  : out std_logic;                                         -- tx_p_out4
            tx_p_out5                  : out std_logic;                                         -- tx_p_out5
            tx_p_out6                  : out std_logic;                                         -- tx_p_out6
            tx_p_out7                  : out std_logic;                                         -- tx_p_out7
            tx_p_out8                  : out std_logic;                                         -- tx_p_out8
            tx_p_out9                  : out std_logic;                                         -- tx_p_out9
            tx_p_out10                 : out std_logic;                                         -- tx_p_out10
            tx_p_out11                 : out std_logic;                                         -- tx_p_out11
            tx_p_out12                 : out std_logic;                                         -- tx_p_out12
            tx_p_out13                 : out std_logic;                                         -- tx_p_out13
            tx_p_out14                 : out std_logic;                                         -- tx_p_out14
            tx_p_out15                 : out std_logic;                                         -- tx_p_out15
            coreclkout_hip             : out std_logic;                                         -- clk
            refclk0                    : in  std_logic                      := 'X';             -- clk
            refclk1                    : in  std_logic                      := 'X';             -- clk
            pin_perst_n                : in  std_logic                      := 'X';             -- pin_perst
            ninit_done                 : in  std_logic                      := 'X'              -- ninit_done
        );
    end component ptile_pcie_2x8;
    
    constant VSEC_BASE_ADDRESS : integer := 16#D00#;
    constant PCIE_EPS_INST     : natural := tsel(ENDPOINT_MODE=0,PCIE_CONS,2*PCIE_CONS);

    constant DBG_ENABLE              : boolean := PCIE_CORE_DEBUG_ENABLE;
    -- Number of watched signals.
    constant DBG_EVENT_SIGNALS       : natural := 4;
    -- Number of ranges (watched events) per each signal.
    -- Currently, there are 4 ranges for each of the signals.
    constant DBG_EVENT_RANGES        : i_array_t(DBG_EVENT_SIGNALS-1 downto 0) := (others => 4);
    -- Total number of watched events (all ranges for all signals).
    constant DBG_EVENTS              : natural := sum(DBG_EVENT_RANGES);
    -- Address offset for each Event Counter.
    constant DBG_EVENT_OFFSET        : natural := 16#10#;
    constant DBG_MAX_INTERVAL_CYCLES : natural := 2**24-1;
    constant DBG_MAX_INTERVALS       : natural := 1024;
    constant DBG_MI_INTERVAL_ADDR    : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(0 , MI_WIDTH));
    constant DBG_MI_EVENTS_ADDR      : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(4 , MI_WIDTH));
    constant DBG_MI_CAPTURE_EN_ADDR  : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(8 , MI_WIDTH));
    constant DBG_MI_CAPTURE_RD_ADDR  : std_logic_vector(MI_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(12, MI_WIDTH));
    constant DBG_MI_ADDR_MASK        : std_logic_vector(MI_WIDTH-1 downto 0) := (3 downto 2 => '1', others => '0');
    -- Number of Streaming Debug Probes per each PCIe Endpoint.
    -- Need 2 for 1x16 a there are two independent AVST buses.
    constant DBG_PROBES              : natural := tsel(ENDPOINT_MODE=0,2,1);
    -- Address offset for each Streaming Debug Probe.
    constant DBG_PROBE_OFFSET        : natural := 16#40#;
    -- Address offset of all Debug Probes per Endpoint.
    constant DBG_PROBES_OFFSET       : natural := DBG_PROBES*DBG_PROBE_OFFSET;
    -- Array of names (4-letter IDs) of Streaming Debug Probes
    -- This constant contains just the names of Probes of a single Streaming Debug Master.
    -- 2 Probes for 1x16 mode (there are 2 Avalon streams for one Endpoint).
    constant DBG_PROBE_STR           : string := tsel(ENDPOINT_MODE=0,"PRQ0PRQ1","PRQ0"); -- (PRQ0 = PCIe RQ 0)
    -- Address offset for each Endpoint (containing the Debug Probes and Event Counters).
    constant ENDPT_OFFSET            : natural := DBG_PROBES*DBG_PROBE_OFFSET + DBG_EVENTS*DBG_EVENT_OFFSET;

    -- Address bases for Endpoints
    function mi_addr_base_endpts_f return slv_array_t is
        variable mi_addr_base : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    begin
        for pe in 0 to PCIE_ENDPOINTS-1 loop
            mi_addr_base(pe) := std_logic_vector(to_unsigned(pe*ENDPT_OFFSET, MI_WIDTH));
        end loop;
        return mi_addr_base;
    end function;

    -- Address bases for all Debug Probes and Event Counters in a single Endpoint
    function mi_addr_base_dbg_f return slv_array_t is
        variable mi_addr_base : slv_array_t(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    begin
        mi_addr_base(0) := (others => '0');
        for e in 0 to DBG_EVENTS-1 loop
            mi_addr_base(e+1) := std_logic_vector(to_unsigned(DBG_PROBES_OFFSET + e*DBG_EVENT_OFFSET, MI_WIDTH));
        end loop;
        return mi_addr_base;
    end function;

    signal pcie_reset_status_n      : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_reset_status        : std_logic_vector(PCIE_EPS_INST-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_EPS_INST-1 downto 0);
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
    signal mi_split_dwr         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_addr        : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_be          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_rd          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_wr          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_ardy        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_drd         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_drdy        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_sync_dwr          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_addr         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_be           : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_sync_rd           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_wr           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_ardy         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_drd          : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_drdy         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_split_dbg_dwr     : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_addr    : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_be      : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_dbg_rd      : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_wr      : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_ardy    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_drd     : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_drdy    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);

    signal dp_out_src_rdy       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);
    signal dp_out_dst_rdy       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);

    -- Watched signals:
    -- 4 signals, each with 4 ranges => 4 bits for each watched signal
    -- Any changes and addition of other signals must be also reflected in constants (DBG_EVENT_SIGNALS, DBG_EVENT_RANGES)
    signal eve_ph               : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd               : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph              : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd              : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal eve_ph_reg           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd_reg           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal eve_all_reg          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_EVENTS-1 downto 0);

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

begin

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_core_g : for i in 0 to PCIE_CONS-1 generate       
        pcie_core_1x16_g : if ENDPOINT_MODE = 0 generate
            pcie_core_i : component ptile_pcie_1x16
            port map (
                p0_rx_st_ready_i             => pcie_avst_down_ready(i),             --          p0_rx_st.ready
                p0_rx_st_sop_o               => pcie_avst_down_sop(i),               --                  .startofpacket
                p0_rx_st_eop_o               => pcie_avst_down_eop(i),               --                  .endofpacket
                p0_rx_st_data_o              => pcie_avst_down_data(i),              --                  .data
                p0_rx_st_valid_o             => pcie_avst_down_valid(i),             --                  .valid
                p0_rx_st_empty_o             => pcie_avst_down_empty(i),             --                  .empty
                p0_rx_st_hdr_o               => pcie_avst_down_hdr(i),               --     p0_rx_st_misc.rx_st_hdr
                p0_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i),            --                  .rx_st_tlp_prfx
                p0_rx_st_bar_range_o         => pcie_avst_down_bar_range(i),         --                  .rx_st_bar_range
                p0_rx_st_tlp_abort_o         => open,                           --                  .rx_st_tlp_abort
                p0_rx_par_err_o              => open,                           --                  .rx_par_err
                p0_tx_st_sop_i               => pcie_avst_up_sop(i),                 --          p0_tx_st.startofpacket
                p0_tx_st_eop_i               => pcie_avst_up_eop(i),                 --                  .endofpacket
                p0_tx_st_data_i              => pcie_avst_up_data(i),                --                  .data
                p0_tx_st_valid_i             => pcie_avst_up_valid(i),               --                  .valid
                p0_tx_st_err_i               => pcie_avst_up_error(i),               --                  .error
                p0_tx_st_ready_o             => pcie_avst_up_ready(i),               --                  .ready
                p0_tx_st_hdr_i               => pcie_avst_up_hdr(i),                 --     p0_tx_st_misc.tx_st_hdr
                p0_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i),              --                  .tx_st_tlp_prfx
                p0_tx_par_err_o              => open,                           --                  .tx_par_err
                p0_tx_cdts_limit_o           => pcie_dbg_credits(i*2),                           --        p0_tx_cred.tx_cdts_type
                p0_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2),                           --                  .tx_data_cdts_consumed
                p0_tl_cfg_func_o             => pcie_cfg_func(i),               --      p0_config_tl.tl_cfg_func
                p0_tl_cfg_add_o              => pcie_cfg_addr(i),               --                  .tl_cfg_add
                p0_tl_cfg_ctl_o              => pcie_cfg_data(i),               --                  .tl_cfg_ctl
                p0_dl_timer_update_o         => open,                           --                  .dl_timer_update
                p0_reset_status_n            => pcie_reset_status_n(i),         -- p0_reset_status_n.reset_n
                p0_pin_perst_n               => open,                           --      p0_pin_perst.pin_perst
                p0_link_up_o                 => pcie_link_up_comb(i),           --     p0_power_mgnt.link_up
                p0_dl_up_o                   => open,                           --                  .dl_up
                p0_surprise_down_err_o       => open,                           --                  .surprise_down_err
                p0_pm_state_o                => open,                           --                  .pm_state
                p0_ltssm_state_o             => open,                           --                  .ltssmstate
                p0_pm_dstate_o               => open,                           --                  .pm_dstate
                p0_apps_pm_xmt_pme_i         => (others => '0'),                --                  .apps_pm_xmt_pme
                p0_app_req_retry_en_i        => (others => '0'),                --                  .app_req_retry_en
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i),       --            p0_cii.hdr_poisoned
                p0_cii_override_en_i         => pcie_cii_override_en(i),        --                  .override_en
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i),       --                  .hdr_first_be
                p0_cii_dout_o                => pcie_cii_dout(i),               --                  .dout
                p0_cii_halt_i                => pcie_cii_halt(i),               --                  .halt
                p0_cii_req_o                 => pcie_cii_req(i),                --                  .req
                p0_cii_addr_o                => pcie_cii_addr(i),               --                  .addr
                p0_cii_wr_o                  => pcie_cii_wr(i),                 --                  .write
                p0_cii_override_din_i        => pcie_cii_override_din(i),       --                  .override_din
                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),      --        hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),      --                  .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),      --                  .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),      --                  .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),      --                  .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),      --                  .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),      --                  .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),      --                  .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),      --                  .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),      --                  .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),     --                  .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),     --                  .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),     --                  .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),     --                  .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),     --                  .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),     --                  .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),      --                  .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),      --                  .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),      --                  .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),      --                  .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),      --                  .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),      --                  .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),      --                  .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),      --                  .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),      --                  .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),      --                  .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),     --                  .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),     --                  .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),     --                  .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),     --                  .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),     --                  .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),     --                  .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),      --                  .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),      --                  .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),      --                  .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),      --                  .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),      --                  .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),      --                  .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),      --                  .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),      --                  .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),      --                  .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),      --                  .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),     --                  .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),     --                  .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),     --                  .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),     --                  .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),     --                  .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),     --                  .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),      --                  .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),      --                  .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),      --                  .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),      --                  .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),      --                  .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),      --                  .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),      --                  .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),      --                  .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),      --                  .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),      --                  .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),     --                  .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),     --                  .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),     --                  .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),     --                  .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),     --                  .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15),     --                  .tx_p_out15
                coreclkout_hip               => pcie_hip_clk(i),                --    coreclkout_hip.clk
                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),       --           refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),     --           refclk1.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),               --         pin_perst.pin_perst
                ninit_done                   => pcie_init_done_n(i)             --        ninit_done.ninit_done
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
                p0_rx_st_ready_i             => pcie_avst_down_ready(i*2),             --          p0_rx_st.ready
                p0_rx_st_sop_o               => pcie_avst_down_sop(i*2),               --                  .startofpacket
                p0_rx_st_eop_o               => pcie_avst_down_eop(i*2),               --                  .endofpacket
                p0_rx_st_data_o              => pcie_avst_down_data(i*2),              --                  .data
                p0_rx_st_valid_o             => pcie_avst_down_valid(i*2),             --                  .valid
                p0_rx_st_empty_o             => pcie_avst_down_empty(i*2),             --                  .empty
                p0_rx_st_hdr_o               => pcie_avst_down_hdr(i*2),               --     p0_rx_st_misc.rx_st_hdr
                p0_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i*2),            --                  .rx_st_tlp_prfx
                p0_rx_st_bar_range_o         => pcie_avst_down_bar_range(i*2),         --                  .rx_st_bar_range
                p0_rx_st_tlp_abort_o         => open,                           --                  .rx_st_tlp_abort
                p0_rx_par_err_o              => open,                           --                  .rx_par_err
                p0_tx_st_sop_i               => pcie_avst_up_sop(i*2),                 --          p0_tx_st.startofpacket
                p0_tx_st_eop_i               => pcie_avst_up_eop(i*2),                 --                  .endofpacket
                p0_tx_st_data_i              => pcie_avst_up_data(i*2),                --                  .data
                p0_tx_st_valid_i             => pcie_avst_up_valid(i*2),               --                  .valid
                p0_tx_st_err_i               => pcie_avst_up_error(i*2),               --                  .error
                p0_tx_st_ready_o             => pcie_avst_up_ready(i*2),               --                  .ready
                p0_tx_st_hdr_i               => pcie_avst_up_hdr(i*2),                 --     p0_tx_st_misc.tx_st_hdr
                p0_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i*2),              --                  .tx_st_tlp_prfx
                p0_tx_par_err_o              => open,                           --                  .tx_par_err
                p0_tx_cdts_limit_o           => pcie_dbg_credits(i*2),                           --        p0_tx_cred.tx_cdts_type
                p0_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2),                           --                  .tx_data_cdts_consumed
                p0_tl_cfg_func_o             => pcie_cfg_func(i*2),               --      p0_config_tl.tl_cfg_func
                p0_tl_cfg_add_o              => pcie_cfg_addr(i*2),               --                  .tl_cfg_add
                p0_tl_cfg_ctl_o              => pcie_cfg_data(i*2),               --                  .tl_cfg_ctl
                p0_dl_timer_update_o         => open,                           --                  .dl_timer_update
                p0_reset_status_n            => pcie_reset_status_n(i*2),         -- p0_reset_status_n.reset_n
                p0_pin_perst_n               => open,                           --      p0_pin_perst.pin_perst
                p0_link_up_o                 => pcie_link_up_comb(i*2),           --     p0_power_mgnt.link_up
                p0_dl_up_o                   => open,                           --                  .dl_up
                p0_surprise_down_err_o       => open,                           --                  .surprise_down_err
                p0_pm_state_o                => open,                           --                  .pm_state
                p0_ltssm_state_o             => open,                           --                  .ltssmstate
                p0_pm_dstate_o               => open,                           --                  .pm_dstate
                p0_apps_pm_xmt_pme_i         => (others => '0'),                --                  .apps_pm_xmt_pme
                p0_app_req_retry_en_i        => (others => '0'),                --                  .app_req_retry_en
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2),       --            p0_cii.hdr_poisoned
                p0_cii_override_en_i         => pcie_cii_override_en(i*2),        --                  .override_en
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2),       --                  .hdr_first_be
                p0_cii_dout_o                => pcie_cii_dout(i*2),               --                  .dout
                p0_cii_halt_i                => pcie_cii_halt(i*2),               --                  .halt
                p0_cii_req_o                 => pcie_cii_req(i*2),                --                  .req
                p0_cii_addr_o                => pcie_cii_addr(i*2),               --                  .addr
                p0_cii_wr_o                  => pcie_cii_wr(i*2),                 --                  .write
                p0_cii_override_din_i        => pcie_cii_override_din(i*2),       --                  .override_din
                
                p1_rx_st_ready_i             => pcie_avst_down_ready(i*2+1),             --          p0_rx_st.ready
                p1_rx_st_sop_o               => pcie_avst_down_sop(i*2+1),               --                  .startofpacket
                p1_rx_st_eop_o               => pcie_avst_down_eop(i*2+1),               --                  .endofpacket
                p1_rx_st_data_o              => pcie_avst_down_data(i*2+1),              --                  .data
                p1_rx_st_valid_o             => pcie_avst_down_valid(i*2+1),             --                  .valid
                p1_rx_st_empty_o             => pcie_avst_down_empty(i*2+1),             --                  .empty
                p1_rx_st_hdr_o               => pcie_avst_down_hdr(i*2+1),               --     p0_rx_st_misc.rx_st_hdr
                p1_rx_st_tlp_prfx_o          => pcie_avst_down_prefix(i*2+1),            --                  .rx_st_tlp_prfx
                p1_rx_st_bar_range_o         => pcie_avst_down_bar_range(i*2+1),         --                  .rx_st_bar_range
                p1_rx_st_tlp_abort_o         => open,                           --                  .rx_st_tlp_abort
                p1_rx_par_err_o              => open,                           --                  .rx_par_err
                p1_tx_st_sop_i               => pcie_avst_up_sop(i*2+1),                 --          p0_tx_st.startofpacket
                p1_tx_st_eop_i               => pcie_avst_up_eop(i*2+1),                 --                  .endofpacket
                p1_tx_st_data_i              => pcie_avst_up_data(i*2+1),                --                  .data
                p1_tx_st_valid_i             => pcie_avst_up_valid(i*2+1),               --                  .valid
                p1_tx_st_err_i               => pcie_avst_up_error(i*2+1),               --                  .error
                p1_tx_st_ready_o             => pcie_avst_up_ready(i*2+1),               --                  .ready
                p1_tx_st_hdr_i               => pcie_avst_up_hdr(i*2+1),                 --     p0_tx_st_misc.tx_st_hdr
                p1_tx_st_tlp_prfx_i          => pcie_avst_up_prefix(i*2+1),              --                  .tx_st_tlp_prfx
                p1_tx_par_err_o              => open,                           --                  .tx_par_err
                p1_tx_cdts_limit_o           => pcie_dbg_credits(i*2+1),                           --        p0_tx_cred.tx_cdts_type
                p1_tx_cdts_limit_tdm_idx_o   => pcie_dbg_credits_sel(i*2+1),                           --                  .tx_data_cdts_consumed
                p1_tl_cfg_func_o             => pcie_cfg_func(i*2+1),               --      p0_config_tl.tl_cfg_func
                p1_tl_cfg_add_o              => pcie_cfg_addr(i*2+1),               --                  .tl_cfg_add
                p1_tl_cfg_ctl_o              => pcie_cfg_data(i*2+1),               --                  .tl_cfg_ctl
                p1_dl_timer_update_o         => open,                           --                  .dl_timer_update
                p1_reset_status_n            => pcie_reset_status_n(i*2+1),         -- p0_reset_status_n.reset_n
                p1_pin_perst_n               => open,                           --      p0_pin_perst.pin_perst
                p1_link_up_o                 => pcie_link_up_comb(i*2+1),           --     p0_power_mgnt.link_up
                p1_dl_up_o                   => open,                           --                  .dl_up
                p1_surprise_down_err_o       => open,                           --                  .surprise_down_err
                p1_pm_state_o                => open,                           --                  .pm_state
                p1_ltssm_state_o             => open,                           --                  .ltssmstate
                p1_pm_dstate_o               => open,                           --                  .pm_dstate
                p1_apps_pm_xmt_pme_i         => (others => '0'),                --                  .apps_pm_xmt_pme
                p1_app_req_retry_en_i        => (others => '0'),                --                  .app_req_retry_en
                p1_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2+1),       --            p0_cii.hdr_poisoned
                p1_cii_override_en_i         => pcie_cii_override_en(i*2+1),        --                  .override_en
                p1_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2+1),       --                  .hdr_first_be
                p1_cii_dout_o                => pcie_cii_dout(i*2+1),               --                  .dout
                p1_cii_halt_i                => pcie_cii_halt(i*2+1),               --                  .halt
                p1_cii_req_o                 => pcie_cii_req(i*2+1),                --                  .req
                p1_cii_addr_o                => pcie_cii_addr(i*2+1),               --                  .addr
                p1_cii_wr_o                  => pcie_cii_wr(i*2+1),                 --                  .write
                p1_cii_override_din_i        => pcie_cii_override_din(i*2+1),       --                  .override_din

                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),      --        hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),      --                  .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),      --                  .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),      --                  .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),      --                  .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),      --                  .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),      --                  .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),      --                  .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),      --                  .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),      --                  .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),     --                  .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),     --                  .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),     --                  .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),     --                  .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),     --                  .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),     --                  .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),      --                  .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),      --                  .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),      --                  .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),      --                  .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),      --                  .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),      --                  .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),      --                  .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),      --                  .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),      --                  .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),      --                  .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),     --                  .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),     --                  .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),     --                  .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),     --                  .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),     --                  .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),     --                  .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),      --                  .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),      --                  .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),      --                  .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),      --                  .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),      --                  .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),      --                  .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),      --                  .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),      --                  .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),      --                  .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),      --                  .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),     --                  .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),     --                  .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),     --                  .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),     --                  .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),     --                  .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),     --                  .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),      --                  .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),      --                  .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),      --                  .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),      --                  .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),      --                  .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),      --                  .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),      --                  .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),      --                  .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),      --                  .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),      --                  .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),     --                  .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),     --                  .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),     --                  .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),     --                  .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),     --                  .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15),     --                  .tx_p_out15
                coreclkout_hip               => pcie_hip_clk(i),                --    coreclkout_hip.clk
                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),       --           refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),     --           refclk1.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),               --         pin_perst.pin_perst
                ninit_done                   => pcie_init_done_n(i)             --        ninit_done.ninit_done
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
        --TODO insert pcie function to HDR

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
        constant dt_en : boolean := (i = 0);
    begin
        cii2cfg_ext_i: entity work.PCIE_CII2CFG_EXT
        port map(
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
        generic map(
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => dt_en,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => 16#000#,
            CARD_ID_WIDTH          => CARD_ID_WIDTH,
            CFG_EXT_READ_DV_HOTFIX => false
        )
        port map(
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

    debug_logic_g : if DBG_ENABLE generate

        mi_splitter_endpts_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH => MI_WIDTH             ,
            DATA_WIDTH => MI_WIDTH             ,
            PORTS      => PCIE_ENDPOINTS       ,
            ADDR_BASE  => mi_addr_base_endpts_f,
            PIPE_OUT   => (others => false)    ,
            DEVICE     => DEVICE
        )
        port map(
            CLK     => MI_CLK       ,
            RESET   => MI_RESET     ,

            RX_DWR  => MI_DWR       ,
            RX_ADDR => MI_ADDR      ,
            RX_BE   => MI_BE        ,
            RX_RD   => MI_RD        ,
            RX_WR   => MI_WR        ,
            RX_ARDY => MI_ARDY      ,
            RX_DRD  => MI_DRD       ,
            RX_DRDY => MI_DRDY      ,

            TX_DWR  => mi_split_dwr ,
            TX_ADDR => mi_split_addr,
            TX_BE   => mi_split_be  ,
            TX_RD   => mi_split_rd  ,
            TX_WR   => mi_split_wr  ,
            TX_ARDY => mi_split_ardy,
            TX_DRD  => mi_split_drd ,
            TX_DRDY => mi_split_drdy
        );

        pcie_endpoints_dbg_g : for pe in 0 to PCIE_ENDPOINTS-1 generate

            -- ----------
            --  MI Async
            -- ----------
            mi_async_i : entity work.MI_ASYNC
            generic map(
                DEVICE => DEVICE
            )
            port map(
                CLK_M     => MI_CLK,
                RESET_M   => MI_RESET,
                MI_M_DWR  => mi_split_dwr (pe)   ,
                MI_M_ADDR => mi_split_addr(pe)   ,
                MI_M_RD   => mi_split_rd  (pe)   ,
                MI_M_WR   => mi_split_wr  (pe)   ,
                MI_M_BE   => mi_split_be  (pe)   ,
                MI_M_DRD  => mi_split_drd (pe)   ,
                MI_M_ARDY => mi_split_ardy(pe)   ,
                MI_M_DRDY => mi_split_drdy(pe)   ,

                CLK_S     => pcie_clk     (pe)   ,
                RESET_S   => pcie_rst     (pe)(0),
                MI_S_DWR  => mi_sync_dwr  (pe)   ,
                MI_S_ADDR => mi_sync_addr (pe)   ,
                MI_S_RD   => mi_sync_rd   (pe)   ,
                MI_S_WR   => mi_sync_wr   (pe)   ,
                MI_S_BE   => mi_sync_be   (pe)   ,
                MI_S_DRD  => mi_sync_drd  (pe)   ,
                MI_S_ARDY => mi_sync_ardy (pe)   ,
                MI_S_DRDY => mi_sync_drdy (pe)
            );

            -- ----------------------------------------------------
            --  MI Splitter for all MI interfaces in each Endpoint
            -- ----------------------------------------------------
            mi_splitter_debug_i : entity work.MI_SPLITTER_PLUS_GEN
            generic map(
                ADDR_WIDTH => MI_WIDTH          ,
                DATA_WIDTH => MI_WIDTH          ,
                PORTS      => 1+DBG_EVENTS      ,
                ADDR_BASE  => mi_addr_base_dbg_f,
                PIPE_OUT   => (others => true)  ,
                DEVICE     => DEVICE
            )
            port map(
                CLK     => pcie_clk         (pe)   ,
                RESET   => pcie_rst         (pe)(0),

                RX_DWR  => mi_sync_dwr      (pe)   ,
                RX_ADDR => mi_sync_addr     (pe)   ,
                RX_BE   => mi_sync_be       (pe)   ,
                RX_RD   => mi_sync_rd       (pe)   ,
                RX_WR   => mi_sync_wr       (pe)   ,
                RX_ARDY => mi_sync_ardy     (pe)   ,
                RX_DRD  => mi_sync_drd      (pe)   ,
                RX_DRDY => mi_sync_drdy     (pe)   ,

                TX_DWR  => mi_split_dbg_dwr (pe)   ,
                TX_ADDR => mi_split_dbg_addr(pe)   ,
                TX_BE   => mi_split_dbg_be  (pe)   ,
                TX_RD   => mi_split_dbg_rd  (pe)   ,
                TX_WR   => mi_split_dbg_wr  (pe)   ,
                TX_ARDY => mi_split_dbg_ardy(pe)   ,
                TX_DRD  => mi_split_dbg_drd (pe)   ,
                TX_DRDY => mi_split_dbg_drdy(pe)
            );

            -- -----------------------------------------------
            --  Streaming Debug Master for each PCIe Endpoint
            -- -----------------------------------------------
            debug_master_i : entity work.STREAMING_DEBUG_MASTER
            generic map(
                CONNECTED_PROBES   => DBG_PROBES              ,
                REGIONS            => RQ_MFB_REGIONS          ,
                DEBUG_ENABLED      => true                    ,
                PROBE_ENABLED      => (1 to DBG_PROBES => 'E'),
                COUNTER_WORD       => (1 to DBG_PROBES => 'E'),
                COUNTER_WAIT       => (1 to DBG_PROBES => 'E'),
                COUNTER_DST_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SRC_HOLD   => (1 to DBG_PROBES => 'E'),
                COUNTER_SOP        => (1 to DBG_PROBES => 'D'), -- disabled
                COUNTER_EOP        => (1 to DBG_PROBES => 'D'), -- disabled
                BUS_CONTROL        => (1 to DBG_PROBES => 'D'), -- disabled
                PROBE_NAMES        => DBG_PROBE_STR           ,
                DEBUG_REG          => true
            )
            port map(
                CLK           => pcie_clk         (pe)   ,
                RESET         => pcie_rst         (pe)(0),

                MI_DWR        => mi_split_dbg_dwr (pe)(0),
                MI_ADDR       => mi_split_dbg_addr(pe)(0),
                MI_RD         => mi_split_dbg_rd  (pe)(0),
                MI_WR         => mi_split_dbg_wr  (pe)(0),
                MI_BE         => mi_split_dbg_be  (pe)(0),
                MI_DRD        => mi_split_dbg_drd (pe)(0),
                MI_ARDY       => mi_split_dbg_ardy(pe)(0),
                MI_DRDY       => mi_split_dbg_drdy(pe)(0),

                DEBUG_BLOCK   => open                    ,
                DEBUG_DROP    => open                    ,
                DEBUG_SOP     => (others => '0')         ,
                DEBUG_EOP     => (others => '0')         ,
                DEBUG_SRC_RDY => dp_out_src_rdy   (pe)   ,
                DEBUG_DST_RDY => dp_out_dst_rdy   (pe)
            );

            debug_probes_g : for dp in 0 to DBG_PROBES-1 generate
                debug_probe_i : entity work.STREAMING_DEBUG_PROBE_MFB
                generic map(
                    REGIONS => RQ_MFB_REGIONS -- CC or RQ?
                )
                port map(
                    RX_SOF         => (others => '0')           , -- SOP counters are unecessary => disabled in the Master Probe
                    RX_EOF         => (others => '0')           , -- EOP counters are unecessary => disabled in the Master Probe
                    RX_SRC_RDY     => pcie_avst_up_valid(pe)(dp),
                    RX_DST_RDY     => open                      ,

                    TX_SOF         => open                      ,
                    TX_EOF         => open                      ,
                    TX_SRC_RDY     => open                      ,
                    TX_DST_RDY     => pcie_avst_up_ready(pe)    , -- PCIe 1x16 has 2 buses with a common DST RDY

                    DEBUG_BLOCK    => '0'                       ,
                    DEBUG_DROP     => '0'                       ,
                    DEBUG_SOF      => open                      ,
                    DEBUG_EOF      => open                      ,
                    DEBUG_SRC_RDY  => dp_out_src_rdy    (pe)(dp),
                    DEBUG_DST_RDY  => dp_out_dst_rdy    (pe)(dp)
                );
            end generate;

            -- ----------------
            --  Event Counters
            -- ----------------
            eve_cnt_g : for de in 0 to DBG_EVENTS-1 generate
                eve_cnt_i : entity work.EVENT_COUNTER_MI_WRAPPER
                generic map(
                    MAX_INTERVAL_CYCLES   => DBG_MAX_INTERVAL_CYCLES,
                    MAX_CONCURRENT_EVENTS => 1                      ,
                    CAPTURE_EN            => True                   ,
                    CAPTURE_FIFO_ITEMS    => DBG_MAX_INTERVALS      ,
                    MI_WIDTH              => MI_WIDTH               ,
                    MI_INTERVAL_ADDR      => DBG_MI_INTERVAL_ADDR   ,
                    MI_EVENTS_ADDR        => DBG_MI_EVENTS_ADDR     ,
                    MI_CPT_EN_ADDR        => DBG_MI_CAPTURE_EN_ADDR ,
                    MI_CPT_RD_ADDR        => DBG_MI_CAPTURE_RD_ADDR ,
                    MI_ADDR_MASK          => DBG_MI_ADDR_MASK
                )
                port map(
                    CLK       => pcie_clk         (pe)      ,
                    RESET     => pcie_rst         (pe)(0)   ,

                    MI_DWR    => mi_split_dbg_dwr (pe)(de+1),
                    MI_ADDR   => mi_split_dbg_addr(pe)(de+1),
                    MI_RD     => mi_split_dbg_rd  (pe)(de+1),
                    MI_WR     => mi_split_dbg_wr  (pe)(de+1),
                    MI_ARDY   => mi_split_dbg_ardy(pe)(de+1),
                    MI_DRDY   => mi_split_dbg_drdy(pe)(de+1),
                    MI_DRD    => mi_split_dbg_drd (pe)(de+1),

                    EVENT_CNT => (others => '1')            ,
                    EVENT_VLD => eve_all_reg      (pe)(de)
                );
            end generate;

            -- The connection of the four watched signals
            eve_all_reg(pe)(1*4-1 downto 0*4) <= eve_ph_reg (pe); -- Posted Headers
            eve_all_reg(pe)(2*4-1 downto 1*4) <= eve_pd_reg (pe); -- Posted Data
            eve_all_reg(pe)(3*4-1 downto 2*4) <= eve_nph_reg(pe); -- Non-Posted Headers
            eve_all_reg(pe)(4*4-1 downto 3*4) <= eve_npd_reg(pe); -- Non-Posted Data

            -- Posted Headers
            process (pcie_clk(pe))
            begin
                if (rising_edge(pcie_clk(pe))) then
                    eve_ph(pe)(0)  <= dbg_credits_ph_vld(pe) when (unsigned(dbg_credits_ph(pe)) >= 0 ) and (unsigned(dbg_credits_ph(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_ph(pe)(1)  <= dbg_credits_ph_vld(pe) when (unsigned(dbg_credits_ph(pe)) >= 8 ) and (unsigned(dbg_credits_ph(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_ph(pe)(2)  <= dbg_credits_ph_vld(pe) when (unsigned(dbg_credits_ph(pe)) >= 32) and (unsigned(dbg_credits_ph(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_ph(pe)(3)  <= dbg_credits_ph_vld(pe) and (or dbg_credits_ph(pe)(11 downto 7));                                                     -- 127+   available Descriptors
                    eve_ph_reg(pe) <= eve_ph(pe);
                end if;
            end process;

            -- Non-Posted Headers
            process (pcie_clk(pe))
            begin
                if (rising_edge(pcie_clk(pe))) then
                    eve_nph(pe)(0)  <= dbg_credits_nph_vld(pe) when (unsigned(dbg_credits_nph(pe)) >= 0 ) and (unsigned(dbg_credits_nph(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_nph(pe)(1)  <= dbg_credits_nph_vld(pe) when (unsigned(dbg_credits_nph(pe)) >= 8 ) and (unsigned(dbg_credits_nph(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_nph(pe)(2)  <= dbg_credits_nph_vld(pe) when (unsigned(dbg_credits_nph(pe)) >= 32) and (unsigned(dbg_credits_nph(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_nph(pe)(3)  <= dbg_credits_nph_vld(pe) and (or dbg_credits_nph(pe)(11 downto 7));                                                      -- 127+   available Descriptors
                    eve_nph_reg(pe) <= eve_nph(pe);
                end if;
            end process;

            -- Posted Data
            process (pcie_clk(pe))
            begin
                if (rising_edge(pcie_clk(pe))) then
                    eve_pd(pe)(0)  <= dbg_credits_pd_vld(pe) when (unsigned(dbg_credits_pd(pe)) >= 0 ) and (unsigned(dbg_credits_pd(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_pd(pe)(1)  <= dbg_credits_pd_vld(pe) when (unsigned(dbg_credits_pd(pe)) >= 8 ) and (unsigned(dbg_credits_pd(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_pd(pe)(2)  <= dbg_credits_pd_vld(pe) when (unsigned(dbg_credits_pd(pe)) >= 32) and (unsigned(dbg_credits_pd(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_pd(pe)(3)  <= dbg_credits_pd_vld(pe) and (or dbg_credits_pd(pe)(15 downto 7));                                                     -- 127+   available Descriptors
                    eve_pd_reg(pe) <= eve_pd(pe);
                end if;
            end process;

            -- Non-Posted Data
            process (pcie_clk(pe))
            begin
                if (rising_edge(pcie_clk(pe))) then
                    eve_npd(pe)(0)  <= dbg_credits_npd_vld(pe) when (unsigned(dbg_credits_npd(pe)) >= 0 ) and (unsigned(dbg_credits_npd(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_npd(pe)(1)  <= dbg_credits_npd_vld(pe) when (unsigned(dbg_credits_npd(pe)) >= 8 ) and (unsigned(dbg_credits_npd(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_npd(pe)(2)  <= dbg_credits_npd_vld(pe) when (unsigned(dbg_credits_npd(pe)) >= 32) and (unsigned(dbg_credits_npd(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_npd(pe)(3)  <= dbg_credits_npd_vld(pe) and (or dbg_credits_npd(pe)(15 downto 7));                                                      -- 127+   available Descriptors
                    eve_npd_reg(pe) <= eve_npd(pe);
                end if;
            end process;

            dbg_credits_ph (pe) <= pcie_dbg_credits(pe)(11 downto 0); -- "When the traffic type is header credit, only the LSB 12 bits are valid" - Intel doc
            dbg_credits_nph(pe) <= pcie_dbg_credits(pe)(11 downto 0); -- "When the traffic type is header credit, only the LSB 12 bits are valid" - Intel doc
            dbg_credits_pd (pe) <= pcie_dbg_credits(pe);
            dbg_credits_npd(pe) <= pcie_dbg_credits(pe);

            dbg_credits_ph_vld (pe) <= '1' when (pcie_dbg_credits_sel(pe) = "000") else '0'; --     Posted header credit limit
            dbg_credits_nph_vld(pe) <= '1' when (pcie_dbg_credits_sel(pe) = "001") else '0'; -- Non-Posted header credit limit
            dbg_credits_pd_vld (pe) <= '1' when (pcie_dbg_credits_sel(pe) = "100") else '0'; --     Posted data   credit limit
            dbg_credits_npd_vld(pe) <= '1' when (pcie_dbg_credits_sel(pe) = "101") else '0'; -- Non-Posted data   credit limit

        end generate;

    end generate;

end architecture;
