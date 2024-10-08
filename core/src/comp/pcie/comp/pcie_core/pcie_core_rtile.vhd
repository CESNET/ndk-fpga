-- pcie_core_rtile.vhd: PCIe module
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture RTILE of PCIE_CORE is

    component rtile_pcie_2x8 is
        port (
            p0_rx_st_ready_i             : in  std_logic                      := 'X';             -- ready
            p0_rx_st0_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st0_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st0_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st0_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st0_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_rx_st0_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st0_hdr
            p0_rx_st0_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st0_prefix
            p0_rx_st0_hvalid_o           : out std_logic;                                         -- rx_st0_hvalid
            p0_rx_st0_pvalid_o           : out std_logic;                                         -- rx_st0_pvalid
            p0_rx_st0_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st0_bar
            p0_rx_st1_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st1_hdr
            p0_rx_st1_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st1_prefix
            p0_rx_st1_hvalid_o           : out std_logic;                                         -- rx_st1_hvalid
            p0_rx_st1_pvalid_o           : out std_logic;                                         -- rx_st1_pvalid
            p0_rx_st1_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st1_bar
            p0_rx_st_hcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_init
            p0_rx_st_hcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update
            p0_rx_st_hcrdt_update_cnt_i  : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update_cnt
            p0_rx_st_hcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Hcrdt_init_ack
            p0_rx_st_dcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_init
            p0_rx_st_dcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_update
            p0_rx_st_dcrdt_update_cnt_i  : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- rx_st_Dcrdt_update_cnt
            p0_rx_st_dcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Dcrdt_init_ack
            p0_rx_st1_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st1_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st1_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st1_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st1_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_tx_st_hcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_init
            p0_tx_st_hcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_update
            p0_tx_st_hcrdt_update_cnt_o  : out std_logic_vector(5 downto 0);                      -- tx_st_Hcrdt_update_cnt
            p0_tx_st_hcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Hcrdtt_init_ack
            p0_tx_st_dcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_init
            p0_tx_st_dcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_update
            p0_tx_st_dcrdt_update_cnt_o  : out std_logic_vector(11 downto 0);                     -- tx_st_Dcrdt_update_cnt
            p0_tx_st_dcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Dcrdt_init_ack
            p0_tx_st0_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st0_hdr
            p0_tx_st0_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st0_prefix
            p0_tx_st0_hvalid_i           : in  std_logic                      := 'X';             -- tx_st0_hvalid
            p0_tx_st0_pvalid_i           : in  std_logic                      := 'X';             -- tx_st0_pvalid
            p0_tx_st1_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st1_hdr
            p0_tx_st1_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st1_prefix
            p0_tx_st1_hvalid_i           : in  std_logic                      := 'X';             -- tx_st1_hvalid
            p0_tx_st1_pvalid_i           : in  std_logic                      := 'X';             -- tx_st1_pvalid
            p0_tx_st_ready_o             : out std_logic;                                         -- ready
            p0_tx_st0_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st0_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st0_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st0_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_st1_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st1_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st1_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st1_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_ehp_deallocate_empty_o : out std_logic;                                         -- tx_ehp_deallocate_empty
            p1_rx_st_ready_i             : in  std_logic                      := 'X';             -- ready
            p1_rx_st0_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p1_rx_st0_sop_o              : out std_logic;                                         -- startofpacket
            p1_rx_st0_eop_o              : out std_logic;                                         -- endofpacket
            p1_rx_st0_dvalid_o           : out std_logic;                                         -- valid
            p1_rx_st0_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p1_rx_st0_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st0_hdr
            p1_rx_st0_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st0_prefix
            p1_rx_st0_hvalid_o           : out std_logic;                                         -- rx_st0_hvalid
            p1_rx_st0_pvalid_o           : out std_logic;                                         -- rx_st0_pvalid
            p1_rx_st0_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st0_bar
            p1_rx_st1_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st1_hdr
            p1_rx_st1_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st1_prefix
            p1_rx_st1_hvalid_o           : out std_logic;                                         -- rx_st1_hvalid
            p1_rx_st1_pvalid_o           : out std_logic;                                         -- rx_st1_pvalid
            p1_rx_st1_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st1_bar
            p1_rx_st_hcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_init
            p1_rx_st_hcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update
            p1_rx_st_hcrdt_update_cnt_i  : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update_cnt
            p1_rx_st_hcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Hcrdt_init_ack
            p1_rx_st_dcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_init
            p1_rx_st_dcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_update
            p1_rx_st_dcrdt_update_cnt_i  : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- rx_st_Dcrdt_update_cnt
            p1_rx_st_dcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Dcrdt_init_ack
            p1_rx_st1_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p1_rx_st1_sop_o              : out std_logic;                                         -- startofpacket
            p1_rx_st1_eop_o              : out std_logic;                                         -- endofpacket
            p1_rx_st1_dvalid_o           : out std_logic;                                         -- valid
            p1_rx_st1_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p1_tx_st_hcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_init
            p1_tx_st_hcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_update
            p1_tx_st_hcrdt_update_cnt_o  : out std_logic_vector(5 downto 0);                      -- tx_st_Hcrdt_update_cnt
            p1_tx_st_hcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Hcrdtt_init_ack
            p1_tx_st_dcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_init
            p1_tx_st_dcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_update
            p1_tx_st_dcrdt_update_cnt_o  : out std_logic_vector(11 downto 0);                     -- tx_st_Dcrdt_update_cnt
            p1_tx_st_dcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Dcrdt_init_ack
            p1_tx_st0_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st0_hdr
            p1_tx_st0_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st0_prefix
            p1_tx_st0_hvalid_i           : in  std_logic                      := 'X';             -- tx_st0_hvalid
            p1_tx_st0_pvalid_i           : in  std_logic                      := 'X';             -- tx_st0_pvalid
            p1_tx_st1_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st1_hdr
            p1_tx_st1_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st1_prefix
            p1_tx_st1_hvalid_i           : in  std_logic                      := 'X';             -- tx_st1_hvalid
            p1_tx_st1_pvalid_i           : in  std_logic                      := 'X';             -- tx_st1_pvalid
            p1_tx_st_ready_o             : out std_logic;                                         -- ready
            p1_tx_st0_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p1_tx_st0_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p1_tx_st0_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p1_tx_st0_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p1_tx_st1_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p1_tx_st1_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p1_tx_st1_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p1_tx_st1_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p1_tx_ehp_deallocate_empty_o : out std_logic;                                         -- tx_ehp_deallocate_empty
            refclk0                      : in  std_logic                      := 'X';             -- clk
            refclk1                      : in  std_logic                      := 'X';             -- clk
            coreclkout_hip               : out std_logic;                                         -- clk
            pin_perst_n                  : in  std_logic                      := 'X';             -- pin_perst
            pin_perst_n_o                : out std_logic;                                         -- pin_perst_o
            ninit_done                   : in  std_logic                      := 'X';             -- reset
            slow_clk                     : out std_logic;                                         -- clk
            p0_reset_status_n            : out std_logic;                                         -- reset_n
            p0_slow_reset_status_n       : out std_logic;                                         -- reset_n
            p0_link_up_o                 : out std_logic;                                         -- link_up
            p0_dl_up_o                   : out std_logic;                                         -- dl_up
            p0_surprise_down_err_o       : out std_logic;                                         -- surprise_down_err
            p0_dl_timer_update_o         : out std_logic;                                         -- dl_timer_update
            p0_ltssm_state_delay_o       : out std_logic_vector(5 downto 0);                      -- ltssm_state_delay
            p0_ltssm_st_hipfifo_ovrflw_o : out std_logic;                                         -- ltssm_st_hipfifo_ovrflw
            p0_app_xfer_pending_i        : in  std_logic                      := 'X';             -- app_xfer_pending
            p0_pld_gp_status_i           : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- status
            p0_pld_gp_ctrl_o             : out std_logic_vector(7 downto 0);                      -- ctrl
            p0_pld_gp_status_ready_o     : out std_logic;                                         -- status_ready
            p0_cii_req_o                 : out std_logic;                                         -- req
            p0_cii_hdr_poisoned_o        : out std_logic;                                         -- hdr_poisoned
            p0_cii_hdr_first_be_o        : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p0_cii_wr_o                  : out std_logic;                                         -- wr
            p0_cii_addr_o                : out std_logic_vector(9 downto 0);                      -- addr
            p0_cii_dout_o                : out std_logic_vector(31 downto 0);                     -- dout
            p0_cii_override_en_i         : in  std_logic                      := 'X';             -- override_en
            p0_cii_override_din_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            p0_cii_halt_i                : in  std_logic                      := 'X';             -- halt
            p1_reset_status_n            : out std_logic;                                         -- reset_n
            p1_slow_reset_status_n       : out std_logic;                                         -- reset_n
            p1_link_up_o                 : out std_logic;                                         -- link_up
            p1_dl_up_o                   : out std_logic;                                         -- dl_up
            p1_surprise_down_err_o       : out std_logic;                                         -- surprise_down_err
            p1_dl_timer_update_o         : out std_logic;                                         -- dl_timer_update
            p1_ltssm_state_delay_o       : out std_logic_vector(5 downto 0);                      -- ltssm_state_delay
            p1_ltssm_st_hipfifo_ovrflw_o : out std_logic;                                         -- ltssm_st_hipfifo_ovrflw
            p1_app_xfer_pending_i        : in  std_logic                      := 'X';             -- app_xfer_pending
            p1_pld_gp_status_i           : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- status
            p1_pld_gp_ctrl_o             : out std_logic_vector(7 downto 0);                      -- ctrl
            p1_pld_gp_status_ready_o     : out std_logic;                                         -- status_ready
            p1_cii_req_o                 : out std_logic;                                         -- req
            p1_cii_hdr_poisoned_o        : out std_logic;                                         -- hdr_poisoned
            p1_cii_hdr_first_be_o        : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p1_cii_wr_o                  : out std_logic;                                         -- wr
            p1_cii_addr_o                : out std_logic_vector(9 downto 0);                      -- addr
            p1_cii_dout_o                : out std_logic_vector(31 downto 0);                     -- dout
            p1_cii_override_en_i         : in  std_logic                      := 'X';             -- override_en
            p1_cii_override_din_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            p1_cii_halt_i                : in  std_logic                      := 'X';             -- halt
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
            tx_p_out15                   : out std_logic                                          -- tx_p_out15
        );
    end component rtile_pcie_2x8;

    component rtile_pcie_1x16 is
        port (
            p0_rx_st_ready_i             : in  std_logic                      := 'X';             -- ready
            p0_rx_st0_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st0_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st0_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st0_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st0_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_rx_st0_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st0_hdr
            p0_rx_st0_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st0_prefix
            p0_rx_st0_hvalid_o           : out std_logic;                                         -- rx_st0_hvalid
            p0_rx_st0_pvalid_o           : out std_logic;                                         -- rx_st0_pvalid
            p0_rx_st0_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st0_bar
            p0_rx_st0_pt_parity_o        : out std_logic;                                         -- rx_st0_pt_parity
            p0_rx_st1_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st1_hdr
            p0_rx_st1_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st1_prefix
            p0_rx_st1_hvalid_o           : out std_logic;                                         -- rx_st1_hvalid
            p0_rx_st1_pvalid_o           : out std_logic;                                         -- rx_st1_pvalid
            p0_rx_st1_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st1_bar
            p0_rx_st1_pt_parity_o        : out std_logic;                                         -- rx_st1_pt_parity
            p0_rx_st2_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st2_hdr
            p0_rx_st2_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st2_prefix
            p0_rx_st2_hvalid_o           : out std_logic;                                         -- rx_st2_hvalid
            p0_rx_st2_pvalid_o           : out std_logic;                                         -- rx_st2_pvalid
            p0_rx_st2_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st2_bar
            p0_rx_st2_pt_parity_o        : out std_logic;                                         -- rx_st2_pt_parity
            p0_rx_st3_hdr_o              : out std_logic_vector(127 downto 0);                    -- rx_st3_hdr
            p0_rx_st3_prefix_o           : out std_logic_vector(31 downto 0);                     -- rx_st3_prefix
            p0_rx_st3_hvalid_o           : out std_logic;                                         -- rx_st3_hvalid
            p0_rx_st3_pvalid_o           : out std_logic;                                         -- rx_st3_pvalid
            p0_rx_st3_bar_o              : out std_logic_vector(2 downto 0);                      -- rx_st3_bar
            p0_rx_st3_pt_parity_o        : out std_logic;                                         -- rx_st3_pt_parity
            p0_rx_st_hcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_init
            p0_rx_st_hcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update
            p0_rx_st_hcrdt_update_cnt_i  : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- rx_st_Hcrdt_update_cnt
            p0_rx_st_hcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Hcrdt_init_ack
            p0_rx_st_dcrdt_init_i        : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_init
            p0_rx_st_dcrdt_update_i      : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rx_st_Dcrdt_update
            p0_rx_st_dcrdt_update_cnt_i  : in  std_logic_vector(11 downto 0)  := (others => 'X'); -- rx_st_Dcrdt_update_cnt
            p0_rx_st_dcrdt_init_ack_o    : out std_logic_vector(2 downto 0);                      -- rx_st_Dcrdt_init_ack
            p0_rx_st1_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st1_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st1_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st1_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st1_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_rx_st2_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st2_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st2_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st2_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st2_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_rx_st3_data_o             : out std_logic_vector(255 downto 0);                    -- data
            p0_rx_st3_sop_o              : out std_logic;                                         -- startofpacket
            p0_rx_st3_eop_o              : out std_logic;                                         -- endofpacket
            p0_rx_st3_dvalid_o           : out std_logic;                                         -- valid
            p0_rx_st3_empty_o            : out std_logic_vector(2 downto 0);                      -- empty
            p0_tx_st_hcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_init
            p0_tx_st_hcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Hcrdt_update
            p0_tx_st_hcrdt_update_cnt_o  : out std_logic_vector(5 downto 0);                      -- tx_st_Hcrdt_update_cnt
            p0_tx_st_hcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Hcrdtt_init_ack
            p0_tx_st_dcrdt_init_o        : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_init
            p0_tx_st_dcrdt_update_o      : out std_logic_vector(2 downto 0);                      -- tx_st_Dcrdt_update
            p0_tx_st_dcrdt_update_cnt_o  : out std_logic_vector(11 downto 0);                     -- tx_st_Dcrdt_update_cnt
            p0_tx_st_dcrdt_init_ack_i    : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- tx_st_Dcrdt_init_ack
            p0_tx_st0_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st0_hdr
            p0_tx_st0_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st0_prefix
            p0_tx_st0_hvalid_i           : in  std_logic                      := 'X';             -- tx_st0_hvalid
            p0_tx_st0_pvalid_i           : in  std_logic                      := 'X';             -- tx_st0_pvalid
            p0_tx_st1_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st1_hdr
            p0_tx_st1_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st1_prefix
            p0_tx_st1_hvalid_i           : in  std_logic                      := 'X';             -- tx_st1_hvalid
            p0_tx_st1_pvalid_i           : in  std_logic                      := 'X';             -- tx_st1_pvalid
            p0_tx_st2_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st2_hdr
            p0_tx_st2_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st2_prefix
            p0_tx_st2_hvalid_i           : in  std_logic                      := 'X';             -- tx_st2_hvalid
            p0_tx_st2_pvalid_i           : in  std_logic                      := 'X';             -- tx_st2_pvalid
            p0_tx_st3_hdr_i              : in  std_logic_vector(127 downto 0) := (others => 'X'); -- tx_st3_hdr
            p0_tx_st3_prefix_i           : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- tx_st3_prefix
            p0_tx_st3_hvalid_i           : in  std_logic                      := 'X';             -- tx_st3_hvalid
            p0_tx_st3_pvalid_i           : in  std_logic                      := 'X';             -- tx_st3_pvalid
            p0_tx_st_ready_o             : out std_logic;                                         -- ready
            p0_tx_st0_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st0_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st0_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st0_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_st1_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st1_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st1_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st1_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_st2_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st2_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st2_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st2_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_st3_data_i             : in  std_logic_vector(255 downto 0) := (others => 'X'); -- data
            p0_tx_st3_sop_i              : in  std_logic                      := 'X';             -- startofpacket
            p0_tx_st3_eop_i              : in  std_logic                      := 'X';             -- endofpacket
            p0_tx_st3_dvalid_i           : in  std_logic                      := 'X';             -- valid
            p0_tx_ehp_deallocate_empty_o : out std_logic;                                         -- tx_ehp_deallocate_empty
            p0_reset_status_n            : out std_logic;                                         -- reset_n
            p0_slow_reset_status_n       : out std_logic;                                         -- reset_n
            p0_link_up_o                 : out std_logic;                                         -- link_up
            p0_dl_up_o                   : out std_logic;                                         -- dl_up
            p0_surprise_down_err_o       : out std_logic;                                         -- surprise_down_err
            p0_dl_timer_update_o         : out std_logic;                                         -- dl_timer_update
            p0_ltssm_state_delay_o       : out std_logic_vector(5 downto 0);                      -- ltssm_state_delay
            p0_ltssm_st_hipfifo_ovrflw_o : out std_logic;                                         -- ltssm_st_hipfifo_ovrflw
            p0_app_xfer_pending_i        : in  std_logic                      := 'X';             -- app_xfer_pending
            p0_pld_gp_status_i           : in  std_logic_vector(7 downto 0)   := (others => 'X'); -- status
            p0_pld_gp_ctrl_o             : out std_logic_vector(7 downto 0);                      -- ctrl
            p0_pld_gp_status_ready_o     : out std_logic;                                         -- status_ready
            p0_cii_req_o                 : out std_logic;                                         -- req
            p0_cii_hdr_poisoned_o        : out std_logic;                                         -- hdr_poisoned
            p0_cii_hdr_first_be_o        : out std_logic_vector(3 downto 0);                      -- hdr_first_be
            p0_cii_wr_o                  : out std_logic;                                         -- wr
            p0_cii_addr_o                : out std_logic_vector(9 downto 0);                      -- addr
            p0_cii_dout_o                : out std_logic_vector(31 downto 0);                     -- dout
            p0_cii_override_en_i         : in  std_logic                      := 'X';             -- override_en
            p0_cii_override_din_i        : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- override_din
            p0_cii_halt_i                : in  std_logic                      := 'X';             -- halt
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
            refclk0                      : in  std_logic                      := 'X';             -- clk
            refclk1                      : in  std_logic                      := 'X';             -- clk
            coreclkout_hip               : out std_logic;                                         -- clk
            ninit_done                   : in  std_logic                      := 'X';             -- reset
            slow_clk                     : out std_logic;                                         -- clk
            pin_perst_n                  : in  std_logic                      := 'X';             -- reset_n
            pin_perst_n_o                : out std_logic                                          -- reset_n
        );
    end component rtile_pcie_1x16;
    
    constant VSEC_BASE_ADDRESS : integer := 16#D00#;
    constant PCIE_HIPS         : natural := tsel(ENDPOINT_MODE=0,PCIE_ENDPOINTS,PCIE_ENDPOINTS/2);
    constant MAX_PAYLOAD_SIZE  : natural := 512;
    -- MPS_CODE:
    -- 000b: 128 bytes maximum payload size
    -- 001b: 256 bytes maximum payload size
    -- 010b: 512 bytes maximum payload size
    -- 011b: 1024 bytes maximum payload size
    constant MPS_CODE         : std_logic_vector(2 downto 0) := std_logic_vector(to_unsigned((log2(MAX_PAYLOAD_SIZE)-7),3));
    -- 1credit = 16B = 128b = 4DW
    constant AVST_WORD_CRDT   : natural := (CQ_MFB_REGIONS*256)/128;
    constant CQ_FIFO_ITEMS   : natural := 512;
    constant MTC_FIFO_CRDT    : natural := CQ_FIFO_ITEMS*AVST_WORD_CRDT;
    constant CRDT_TOTAL_XPH   : natural := MTC_FIFO_CRDT/(MAX_PAYLOAD_SIZE/16);

    signal pcie_reset_status_n      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_reset_status        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_slow_clk            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_hip_slow_clk        : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_init_done_n         : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);
    signal pcie_slow_rst            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_avst_down_data      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_down_hdr       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*128-1 downto 0);
    signal pcie_avst_down_prefix    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*32-1 downto 0);
    signal pcie_avst_down_sop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_eop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_empty     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_bar_range : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_valid     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_dvalid    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_hvalid    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_ready     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '1');
    signal pcie_avst_up_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_up_hdr         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*128-1 downto 0);
    signal pcie_avst_up_prefix      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*32-1 downto 0);
    signal pcie_avst_up_sop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_eop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_error       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_valid       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_dvalid      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_hvalid      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_ready       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_avst_up_payload_lv  : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS downto 0);

    signal pcie_hcrdt_up_init       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_hcrdt_up_update     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_hcrdt_up_update_cnt : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(5 downto 0);
    signal pcie_hcrdt_up_init_ack   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_up_init       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_up_update     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_up_update_cnt : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal pcie_dcrdt_up_init_ack   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);

    signal pcie_hcrdt_dw_init       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_hcrdt_dw_update     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_hcrdt_dw_update_cnt : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(5 downto 0);
    signal pcie_hcrdt_dw_init_ack   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_dw_init       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_dw_update     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal pcie_dcrdt_dw_update_cnt : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal pcie_dcrdt_dw_init_ack   : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);

    signal crdt_up_init_done        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal crdt_up_update           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(6-1 downto 0);
    signal crdt_up_cnt_ph           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_up_cnt_nph          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_up_cnt_cplh         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_up_cnt_pd           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal crdt_up_cnt_npd          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal crdt_up_cnt_cpld         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    
    signal crdt_down_init_done      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal crdt_down_update         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(6-1 downto 0);
    signal crdt_down_cnt_ph         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_down_cnt_nph        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_down_cnt_cplh       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2-1 downto 0);
    signal crdt_down_cnt_pd         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal crdt_down_cnt_npd        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal crdt_down_cnt_cpld       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal pcie_link_up_comb        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_link_up_reg         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cii_hdr_poisoned    : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cii_override_en     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal pcie_cii_hdr_first_be    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal pcie_cii_dout            : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal pcie_cii_halt            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal pcie_cii_req             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cii_addr            : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal pcie_cii_wr              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cii_override_din    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0) := (others => (others => '0'));

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_function         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

begin

    --assert ENDPOINT_MODE=1 report "Intel R-Tile Wrapper: Only ENDPOINT_MODE=1 is now implemented!"
    --    severity failure;

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_core_g : for i in 0 to PCIE_HIPS-1 generate
        pcie_core_2x8_g : if ENDPOINT_MODE = 1 generate
            rtile_i : component rtile_pcie_2x8
            port map (
                p0_rx_st_ready_i             => pcie_avst_down_ready(i*2),             --              p0_rx_st0.ready
                p0_rx_st0_data_o             => pcie_avst_down_data(i*2)(256-1 downto 0),             --                       .data
                p0_rx_st0_sop_o              => pcie_avst_down_sop(i*2)(0),              --                       .startofpacket
                p0_rx_st0_eop_o              => pcie_avst_down_eop(i*2)(0),              --                       .endofpacket
                p0_rx_st0_dvalid_o           => pcie_avst_down_dvalid(i*2)(0),           --                       .valid
                p0_rx_st0_empty_o            => pcie_avst_down_empty(i*2)(3-1 downto 0),            --                       .empty
                p0_rx_st0_hdr_o              => pcie_avst_down_hdr(i*2)(128-1 downto 0),              --          p0_rx_st_misc.rx_st0_hdr
                p0_rx_st0_prefix_o           => pcie_avst_down_prefix(i*2)(32-1 downto 0),           --                       .rx_st0_prefix
                p0_rx_st0_hvalid_o           => pcie_avst_down_hvalid(i*2)(0),           --                       .rx_st0_hvalid
                p0_rx_st0_pvalid_o           => open,           --                       .rx_st0_pvalid
                p0_rx_st0_bar_o              => pcie_avst_down_bar_range(i*2)(3-1 downto 0),              --                       .rx_st0_bar
                p0_rx_st1_hdr_o              => pcie_avst_down_hdr(i*2)(256-1 downto 128),              --                       .rx_st1_hdr
                p0_rx_st1_prefix_o           => pcie_avst_down_prefix(i*2)(64-1 downto 32),           --                       .rx_st1_prefix
                p0_rx_st1_hvalid_o           => pcie_avst_down_hvalid(i*2)(1),           --                       .rx_st1_hvalid
                p0_rx_st1_pvalid_o           => open,           --                       .rx_st1_pvalid
                p0_rx_st1_bar_o              => pcie_avst_down_bar_range(i*2)(6-1 downto 3),              --                       .rx_st1_bar

                p0_rx_st_hcrdt_init_i        => pcie_hcrdt_dw_init(i*2),        --                       .rx_st_Hcrdt_init
                p0_rx_st_hcrdt_update_i      => pcie_hcrdt_dw_update(i*2),      --                       .rx_st_Hcrdt_update
                p0_rx_st_hcrdt_update_cnt_i  => pcie_hcrdt_dw_update_cnt(i*2),  --                       .rx_st_Hcrdt_update_cnt
                p0_rx_st_hcrdt_init_ack_o    => pcie_hcrdt_dw_init_ack(i*2),    --                       .rx_st_Hcrdt_init_ack
                p0_rx_st_dcrdt_init_i        => pcie_dcrdt_dw_init(i*2),        --                       .rx_st_Dcrdt_init
                p0_rx_st_dcrdt_update_i      => pcie_dcrdt_dw_update(i*2),      --                       .rx_st_Dcrdt_update
                p0_rx_st_dcrdt_update_cnt_i  => pcie_dcrdt_dw_update_cnt(i*2),  --                       .rx_st_Dcrdt_update_cnt
                p0_rx_st_dcrdt_init_ack_o    => pcie_dcrdt_dw_init_ack(i*2),    --                       .rx_st_Dcrdt_init_ack
                p0_rx_st1_data_o             => pcie_avst_down_data(i*2)(512-1 downto 256),             --              p0_rx_st1.data
                p0_rx_st1_sop_o              => pcie_avst_down_sop(i*2)(1),              --                       .startofpacket
                p0_rx_st1_eop_o              => pcie_avst_down_eop(i*2)(1),              --                       .endofpacket
                p0_rx_st1_dvalid_o           => pcie_avst_down_dvalid(i*2)(1),           --                       .valid
                p0_rx_st1_empty_o            => pcie_avst_down_empty(i*2)(6-1 downto 3),            --                       .empty

                p0_tx_st_hcrdt_init_o        => pcie_hcrdt_up_init(i*2),        --          p0_tx_st_misc.tx_st_Hcrdt_init
                p0_tx_st_hcrdt_update_o      => pcie_hcrdt_up_update(i*2),      --                       .tx_st_Hcrdt_update
                p0_tx_st_hcrdt_update_cnt_o  => pcie_hcrdt_up_update_cnt(i*2),  --                       .tx_st_Hcrdt_update_cnt
                p0_tx_st_hcrdt_init_ack_i    => pcie_hcrdt_up_init_ack(i*2),    --                       .tx_st_Hcrdtt_init_ack
                p0_tx_st_dcrdt_init_o        => pcie_dcrdt_up_init(i*2),        --                       .tx_st_Dcrdt_init
                p0_tx_st_dcrdt_update_o      => pcie_dcrdt_up_update(i*2),      --                       .tx_st_Dcrdt_update
                p0_tx_st_dcrdt_update_cnt_o  => pcie_dcrdt_up_update_cnt(i*2),  --                       .tx_st_Dcrdt_update_cnt
                p0_tx_st_dcrdt_init_ack_i    => pcie_dcrdt_up_init_ack(i*2),    --                       .tx_st_Dcrdt_init_ack

                p0_tx_st0_hdr_i              => pcie_avst_up_hdr(i*2)(128-1 downto 0),              --                       .tx_st0_hdr
                p0_tx_st0_prefix_i           => pcie_avst_up_prefix(i*2)(32-1 downto 0),           --                       .tx_st0_prefix
                p0_tx_st0_hvalid_i           => pcie_avst_up_hvalid(i*2)(0),           --                       .tx_st0_hvalid
                p0_tx_st0_pvalid_i           => '0',           --                       .tx_st0_pvalid
                p0_tx_st1_hdr_i              => pcie_avst_up_hdr(i*2)(256-1 downto 128),              --                       .tx_st1_hdr
                p0_tx_st1_prefix_i           => pcie_avst_up_prefix(i*2)(64-1 downto 32),           --                       .tx_st1_prefix
                p0_tx_st1_hvalid_i           => pcie_avst_up_hvalid(i*2)(1),           --                       .tx_st1_hvalid
                p0_tx_st1_pvalid_i           => '0',           --                       .tx_st1_pvalid
                p0_tx_st_ready_o             => pcie_avst_up_ready(i*2),             --              p0_tx_st0.ready
                p0_tx_st0_data_i             => pcie_avst_up_data(i*2)(256-1 downto 0),             --                       .data
                p0_tx_st0_sop_i              => pcie_avst_up_sop(i*2)(0),              --                       .startofpacket
                p0_tx_st0_eop_i              => pcie_avst_up_eop(i*2)(0),              --                       .endofpacket
                p0_tx_st0_dvalid_i           => pcie_avst_up_dvalid(i*2)(0),           --                       .valid
                p0_tx_st1_data_i             => pcie_avst_up_data(i*2)(512-1 downto 256),             --              p0_tx_st1.data
                p0_tx_st1_sop_i              => pcie_avst_up_sop(i*2)(1),              --                       .startofpacket
                p0_tx_st1_eop_i              => pcie_avst_up_eop(i*2)(1),              --                       .endofpacket
                p0_tx_st1_dvalid_i           => pcie_avst_up_dvalid(i*2)(1),           --                       .valid
                p0_tx_ehp_deallocate_empty_o => open, --              p0_tx_ehp.tx_ehp_deallocate_empty

                p1_rx_st_ready_i             => pcie_avst_down_ready(i*2+1),             --              p0_rx_st0.ready
                p1_rx_st0_data_o             => pcie_avst_down_data(i*2+1)(256-1 downto 0),             --                       .data
                p1_rx_st0_sop_o              => pcie_avst_down_sop(i*2+1)(0),              --                       .startofpacket
                p1_rx_st0_eop_o              => pcie_avst_down_eop(i*2+1)(0),              --                       .endofpacket
                p1_rx_st0_dvalid_o           => pcie_avst_down_dvalid(i*2+1)(0),           --                       .valid
                p1_rx_st0_empty_o            => pcie_avst_down_empty(i*2+1)(3-1 downto 0),            --                       .empty
                p1_rx_st0_hdr_o              => pcie_avst_down_hdr(i*2+1)(128-1 downto 0),              --          p0_rx_st_misc.rx_st0_hdr
                p1_rx_st0_prefix_o           => pcie_avst_down_prefix(i*2+1)(32-1 downto 0),           --                       .rx_st0_prefix
                p1_rx_st0_hvalid_o           => pcie_avst_down_hvalid(i*2+1)(0),           --                       .rx_st0_hvalid
                p1_rx_st0_pvalid_o           => open,           --                       .rx_st0_pvalid
                p1_rx_st0_bar_o              => pcie_avst_down_bar_range(i*2+1)(3-1 downto 0),              --                       .rx_st0_bar
                p1_rx_st1_hdr_o              => pcie_avst_down_hdr(i*2+1)(256-1 downto 128),              --                       .rx_st1_hdr
                p1_rx_st1_prefix_o           => pcie_avst_down_prefix(i*2+1)(64-1 downto 32),           --                       .rx_st1_prefix
                p1_rx_st1_hvalid_o           => pcie_avst_down_hvalid(i*2+1)(1),           --                       .rx_st1_hvalid
                p1_rx_st1_pvalid_o           => open,           --                       .rx_st1_pvalid
                p1_rx_st1_bar_o              => pcie_avst_down_bar_range(i*2+1)(6-1 downto 3),              --                       .rx_st1_bar

                p1_rx_st_hcrdt_init_i        => pcie_hcrdt_dw_init(i*2+1),        --                       .rx_st_Hcrdt_init
                p1_rx_st_hcrdt_update_i      => pcie_hcrdt_dw_update(i*2+1),      --                       .rx_st_Hcrdt_update
                p1_rx_st_hcrdt_update_cnt_i  => pcie_hcrdt_dw_update_cnt(i*2+1),  --                       .rx_st_Hcrdt_update_cnt
                p1_rx_st_hcrdt_init_ack_o    => pcie_hcrdt_dw_init_ack(i*2+1),    --                       .rx_st_Hcrdt_init_ack
                p1_rx_st_dcrdt_init_i        => pcie_dcrdt_dw_init(i*2+1),        --                       .rx_st_Dcrdt_init
                p1_rx_st_dcrdt_update_i      => pcie_dcrdt_dw_update(i*2+1),      --                       .rx_st_Dcrdt_update
                p1_rx_st_dcrdt_update_cnt_i  => pcie_dcrdt_dw_update_cnt(i*2+1),  --                       .rx_st_Dcrdt_update_cnt
                p1_rx_st_dcrdt_init_ack_o    => pcie_dcrdt_dw_init_ack(i*2+1),    --                       .rx_st_Dcrdt_init_ack
                p1_rx_st1_data_o             => pcie_avst_down_data(i*2+1)(512-1 downto 256),             --              p0_rx_st1.data
                p1_rx_st1_sop_o              => pcie_avst_down_sop(i*2+1)(1),              --                       .startofpacket
                p1_rx_st1_eop_o              => pcie_avst_down_eop(i*2+1)(1),              --                       .endofpacket
                p1_rx_st1_dvalid_o           => pcie_avst_down_dvalid(i*2+1)(1),           --                       .valid
                p1_rx_st1_empty_o            => pcie_avst_down_empty(i*2+1)(6-1 downto 3),            --                       .empty

                p1_tx_st_hcrdt_init_o        => pcie_hcrdt_up_init(i*2+1),        --          p1_tx_st_misc.tx_st_Hcrdt_init
                p1_tx_st_hcrdt_update_o      => pcie_hcrdt_up_update(i*2+1),      --                       .tx_st_Hcrdt_update
                p1_tx_st_hcrdt_update_cnt_o  => pcie_hcrdt_up_update_cnt(i*2+1),  --                       .tx_st_Hcrdt_update_cnt
                p1_tx_st_hcrdt_init_ack_i    => pcie_hcrdt_up_init_ack(i*2+1),    --                       .tx_st_Hcrdtt_init_ack
                p1_tx_st_dcrdt_init_o        => pcie_dcrdt_up_init(i*2+1),        --                       .tx_st_Dcrdt_init
                p1_tx_st_dcrdt_update_o      => pcie_dcrdt_up_update(i*2+1),      --                       .tx_st_Dcrdt_update
                p1_tx_st_dcrdt_update_cnt_o  => pcie_dcrdt_up_update_cnt(i*2+1),  --                       .tx_st_Dcrdt_update_cnt
                p1_tx_st_dcrdt_init_ack_i    => pcie_dcrdt_up_init_ack(i*2+1),    --                       .tx_st_Dcrdt_init_ack
                p1_tx_st0_hdr_i              => pcie_avst_up_hdr(i*2+1)(128-1 downto 0),              --                       .tx_st0_hdr
                p1_tx_st0_prefix_i           => pcie_avst_up_prefix(i*2+1)(32-1 downto 0),           --                       .tx_st0_prefix
                p1_tx_st0_hvalid_i           => pcie_avst_up_hvalid(i*2+1)(0),           --                       .tx_st0_hvalid
                p1_tx_st0_pvalid_i           => '0',           --                       .tx_st0_pvalid
                p1_tx_st1_hdr_i              => pcie_avst_up_hdr(i*2+1)(256-1 downto 128),              --                       .tx_st1_hdr
                p1_tx_st1_prefix_i           => pcie_avst_up_prefix(i*2+1)(64-1 downto 32),           --                       .tx_st1_prefix
                p1_tx_st1_hvalid_i           => pcie_avst_up_hvalid(i*2+1)(1),           --                       .tx_st1_hvalid
                p1_tx_st1_pvalid_i           => '0',           --                       .tx_st1_pvalid
                p1_tx_st_ready_o             => pcie_avst_up_ready(i*2+1),             --              p0_tx_st0.ready
                p1_tx_st0_data_i             => pcie_avst_up_data(i*2+1)(256-1 downto 0),             --                       .data
                p1_tx_st0_sop_i              => pcie_avst_up_sop(i*2+1)(0),              --                       .startofpacket
                p1_tx_st0_eop_i              => pcie_avst_up_eop(i*2+1)(0),              --                       .endofpacket
                p1_tx_st0_dvalid_i           => pcie_avst_up_dvalid(i*2+1)(0),           --                       .valid
                p1_tx_st1_data_i             => pcie_avst_up_data(i*2+1)(512-1 downto 256),             --              p0_tx_st1.data
                p1_tx_st1_sop_i              => pcie_avst_up_sop(i*2+1)(1),              --                       .startofpacket
                p1_tx_st1_eop_i              => pcie_avst_up_eop(i*2+1)(1),              --                       .endofpacket
                p1_tx_st1_dvalid_i           => pcie_avst_up_dvalid(i*2+1)(1),           --                       .valid
                p1_tx_ehp_deallocate_empty_o => open, --              p1_tx_ehp.tx_ehp_deallocate_empty

                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),                      --                refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),                      --                refclk1.clk
                coreclkout_hip               => pcie_hip_clk(i),               --         coreclkout_hip.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),                  --              pin_perst.pin_perst
                pin_perst_n_o                => open,
                ninit_done                   => pcie_init_done_n(i),                   --             ninit_done.ninit_done
                slow_clk                     => pcie_hip_slow_clk(i),                    --               slow_clk.clk

                p0_reset_status_n            => pcie_reset_status_n(i*2),            --      p0_reset_status_n.reset_n
                p0_slow_reset_status_n       => open,       -- p0_slow_reset_status_n.reset_n
                p0_link_up_o                 => pcie_link_up_comb(i*2),                 --          p0_hip_status.link_up
                p0_dl_up_o                   => open,                   --                       .dl_up
                p0_surprise_down_err_o       => open,       --                       .surprise_down_err
                p0_dl_timer_update_o         => open,         --                       .dl_timer_update
                p0_ltssm_state_delay_o       => open,       --                       .ltssm_state_delay
                p0_ltssm_st_hipfifo_ovrflw_o => open, --                       .ltssm_st_hipfifo_ovrflw
                p0_app_xfer_pending_i        => '0',        --          p0_power_mgnt.app_xfer_pending
                p0_pld_gp_status_i           => (others => '0'),           --              p0_pld_gp.status
                p0_pld_gp_ctrl_o             => open,             --                       .ctrl
                p0_pld_gp_status_ready_o     => open,     --                       .status_ready
                p0_cii_req_o                 => pcie_cii_req(i*2),                 --                 p0_cii.req
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2),        --                       .hdr_poisoned
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2),        --                       .hdr_first_be
                p0_cii_wr_o                  => pcie_cii_wr(i*2),                  --                       .wr
                p0_cii_addr_o                => pcie_cii_addr(i*2),                --                       .addr
                p0_cii_dout_o                => pcie_cii_dout(i*2),                --                       .dout
                p0_cii_override_en_i         => pcie_cii_override_en(i*2),         --                       .override_en
                p0_cii_override_din_i        => pcie_cii_override_din(i*2),        --                       .override_din
                p0_cii_halt_i                => pcie_cii_halt(i*2),                --                       .halt

                p1_reset_status_n            => pcie_reset_status_n(i*2+1),            --      p1_reset_status_n.reset_n
                p1_slow_reset_status_n       => open,       -- p1_slow_reset_status_n.reset_n
                p1_link_up_o                 => pcie_link_up_comb(i*2+1),                 --          p1_hip_status.link_up
                p1_dl_up_o                   => open,                   --                       .dl_up
                p1_surprise_down_err_o       => open,       --                       .surprise_down_err
                p1_dl_timer_update_o         => open,         --                       .dl_timer_update
                p1_ltssm_state_delay_o       => open,       --                       .ltssm_state_delay
                p1_ltssm_st_hipfifo_ovrflw_o => open, --                       .ltssm_st_hipfifo_ovrflw
                p1_app_xfer_pending_i        => '0',        --          p1_power_mgnt.app_xfer_pending
                p1_pld_gp_status_i           => (others => '0'),           --              p1_pld_gp.status
                p1_pld_gp_ctrl_o             => open,             --                       .ctrl
                p1_pld_gp_status_ready_o     => open,     --                       .status_ready
                p1_cii_req_o                 => pcie_cii_req(i*2+1),                 --                 p0_cii.req
                p1_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i*2+1),        --                       .hdr_poisoned
                p1_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i*2+1),        --                       .hdr_first_be
                p1_cii_wr_o                  => pcie_cii_wr(i*2+1),                  --                       .wr
                p1_cii_addr_o                => pcie_cii_addr(i*2+1),                --                       .addr
                p1_cii_dout_o                => pcie_cii_dout(i*2+1),                --                       .dout
                p1_cii_override_en_i         => pcie_cii_override_en(i*2+1),         --                       .override_en
                p1_cii_override_din_i        => pcie_cii_override_din(i*2+1),        --                       .override_din
                p1_cii_halt_i                => pcie_cii_halt(i*2+1),                --                       .halt

                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),                     --             hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),                     --                       .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),                     --                       .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),                     --                       .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),                     --                       .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),                     --                       .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),                     --                       .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),                     --                       .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),                     --                       .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),                     --                       .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),                    --                       .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),                    --                       .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),                    --                       .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),                    --                       .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),                    --                       .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),                    --                       .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),                     --                       .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),                     --                       .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),                     --                       .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),                     --                       .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),                     --                       .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),                     --                       .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),                     --                       .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),                     --                       .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),                     --                       .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),                     --                       .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),                    --                       .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),                    --                       .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),                    --                       .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),                    --                       .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),                    --                       .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),                    --                       .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),                    --                       .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),                    --                       .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),                    --                       .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),                    --                       .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),                    --                       .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),                    --                       .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),                    --                       .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),                    --                       .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),                    --                       .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),                    --                       .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),                   --                       .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),                   --                       .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),                   --                       .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),                   --                       .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),                   --                       .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),                   --                       .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),                    --                       .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),                    --                       .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),                    --                       .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),                    --                       .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),                    --                       .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),                    --                       .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),                    --                       .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),                    --                       .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),                    --                       .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),                    --                       .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),                   --                       .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),                   --                       .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),                   --                       .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),                   --                       .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),                   --                       .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15)                    --                       .tx_p_out15
            );

            pcie_clk(i*2)   <= pcie_hip_clk(i);
            pcie_clk(i*2+1) <= pcie_hip_clk(i);
            pcie_slow_clk(i*2)   <= pcie_hip_slow_clk(i);
            pcie_slow_clk(i*2+1) <= pcie_hip_slow_clk(i);
            pcie_init_done_n(i) <= INIT_DONE_N;
        end generate;
        pcie_core_1x16_g : if ENDPOINT_MODE = 0 generate
            rtile_i : component rtile_pcie_1x16
            port map (
                p0_rx_st_ready_i             => pcie_avst_down_ready(i),

                p0_rx_st0_data_o             => pcie_avst_down_data(i)(256-1 downto 0),
                p0_rx_st0_sop_o              => pcie_avst_down_sop(i)(0),
                p0_rx_st0_eop_o              => pcie_avst_down_eop(i)(0),
                p0_rx_st0_dvalid_o           => pcie_avst_down_dvalid(i)(0),
                p0_rx_st0_empty_o            => pcie_avst_down_empty(i)(3-1 downto 0),
                p0_rx_st0_hdr_o              => pcie_avst_down_hdr(i)(128-1 downto 0),
                p0_rx_st0_prefix_o           => pcie_avst_down_prefix(i)(32-1 downto 0),
                p0_rx_st0_hvalid_o           => pcie_avst_down_hvalid(i)(0),
                p0_rx_st0_pvalid_o           => open,
                p0_rx_st0_bar_o              => pcie_avst_down_bar_range(i)(3-1 downto 0),

                p0_rx_st1_data_o             => pcie_avst_down_data(i)(512-1 downto 256),
                p0_rx_st1_sop_o              => pcie_avst_down_sop(i)(1),
                p0_rx_st1_eop_o              => pcie_avst_down_eop(i)(1),
                p0_rx_st1_dvalid_o           => pcie_avst_down_dvalid(i)(1),
                p0_rx_st1_empty_o            => pcie_avst_down_empty(i)(6-1 downto 3),
                p0_rx_st1_hdr_o              => pcie_avst_down_hdr(i)(256-1 downto 128),
                p0_rx_st1_prefix_o           => pcie_avst_down_prefix(i)(64-1 downto 32),
                p0_rx_st1_hvalid_o           => pcie_avst_down_hvalid(i)(1),
                p0_rx_st1_pvalid_o           => open,
                p0_rx_st1_bar_o              => pcie_avst_down_bar_range(i)(6-1 downto 3),

                p0_rx_st2_data_o             => pcie_avst_down_data(i)(768-1 downto 512),
                p0_rx_st2_sop_o              => pcie_avst_down_sop(i)(2),
                p0_rx_st2_eop_o              => pcie_avst_down_eop(i)(2),
                p0_rx_st2_dvalid_o           => pcie_avst_down_dvalid(i)(2),
                p0_rx_st2_empty_o            => pcie_avst_down_empty(i)(9-1 downto 6),
                p0_rx_st2_hdr_o              => pcie_avst_down_hdr(i)(384-1 downto 256),
                p0_rx_st2_prefix_o           => pcie_avst_down_prefix(i)(96-1 downto 64),
                p0_rx_st2_hvalid_o           => pcie_avst_down_hvalid(i)(2),
                p0_rx_st2_pvalid_o           => open,
                p0_rx_st2_bar_o              => pcie_avst_down_bar_range(i)(9-1 downto 6),

                p0_rx_st3_data_o             => pcie_avst_down_data(i)(1024-1 downto 768),
                p0_rx_st3_sop_o              => pcie_avst_down_sop(i)(3),
                p0_rx_st3_eop_o              => pcie_avst_down_eop(i)(3),
                p0_rx_st3_dvalid_o           => pcie_avst_down_dvalid(i)(3),
                p0_rx_st3_empty_o            => pcie_avst_down_empty(i)(12-1 downto 9),
                p0_rx_st3_hdr_o              => pcie_avst_down_hdr(i)(512-1 downto 384),
                p0_rx_st3_prefix_o           => pcie_avst_down_prefix(i)(128-1 downto 96),
                p0_rx_st3_hvalid_o           => pcie_avst_down_hvalid(i)(3),
                p0_rx_st3_pvalid_o           => open,
                p0_rx_st3_bar_o              => pcie_avst_down_bar_range(i)(12-1 downto 9),

                p0_rx_st_hcrdt_init_i        => pcie_hcrdt_dw_init(i),        --                       .rx_st_Hcrdt_init
                p0_rx_st_hcrdt_update_i      => pcie_hcrdt_dw_update(i),      --                       .rx_st_Hcrdt_update
                p0_rx_st_hcrdt_update_cnt_i  => pcie_hcrdt_dw_update_cnt(i),  --                       .rx_st_Hcrdt_update_cnt
                p0_rx_st_hcrdt_init_ack_o    => pcie_hcrdt_dw_init_ack(i),    --                       .rx_st_Hcrdt_init_ack
                p0_rx_st_dcrdt_init_i        => pcie_dcrdt_dw_init(i),        --                       .rx_st_Dcrdt_init
                p0_rx_st_dcrdt_update_i      => pcie_dcrdt_dw_update(i),      --                       .rx_st_Dcrdt_update
                p0_rx_st_dcrdt_update_cnt_i  => pcie_dcrdt_dw_update_cnt(i),  --                       .rx_st_Dcrdt_update_cnt
                p0_rx_st_dcrdt_init_ack_o    => pcie_dcrdt_dw_init_ack(i),    --                       .rx_st_Dcrdt_init_ack

                p0_tx_st_ready_o             => pcie_avst_up_ready(i),
                p0_tx_ehp_deallocate_empty_o => open,

                p0_tx_st0_hdr_i              => pcie_avst_up_hdr(i)(128-1 downto 0),
                p0_tx_st0_prefix_i           => pcie_avst_up_prefix(i)(32-1 downto 0),
                p0_tx_st0_hvalid_i           => pcie_avst_up_hvalid(i)(0),
                p0_tx_st0_pvalid_i           => '0',
                p0_tx_st0_data_i             => pcie_avst_up_data(i)(256-1 downto 0),
                p0_tx_st0_sop_i              => pcie_avst_up_sop(i)(0),
                p0_tx_st0_eop_i              => pcie_avst_up_eop(i)(0),
                p0_tx_st0_dvalid_i           => pcie_avst_up_dvalid(i)(0),

                p0_tx_st1_hdr_i              => pcie_avst_up_hdr(i)(256-1 downto 128),
                p0_tx_st1_prefix_i           => pcie_avst_up_prefix(i)(64-1 downto 32),
                p0_tx_st1_hvalid_i           => pcie_avst_up_hvalid(i)(1),
                p0_tx_st1_pvalid_i           => '0',
                p0_tx_st1_data_i             => pcie_avst_up_data(i)(512-1 downto 256),
                p0_tx_st1_sop_i              => pcie_avst_up_sop(i)(1),
                p0_tx_st1_eop_i              => pcie_avst_up_eop(i)(1),
                p0_tx_st1_dvalid_i           => pcie_avst_up_dvalid(i)(1),

                p0_tx_st2_hdr_i              => pcie_avst_up_hdr(i)(384-1 downto 256),
                p0_tx_st2_prefix_i           => pcie_avst_up_prefix(i)(96-1 downto 64),
                p0_tx_st2_hvalid_i           => pcie_avst_up_hvalid(i)(2),
                p0_tx_st2_pvalid_i           => '0',
                p0_tx_st2_data_i             => pcie_avst_up_data(i)(768-1 downto 512),
                p0_tx_st2_sop_i              => pcie_avst_up_sop(i)(2),
                p0_tx_st2_eop_i              => pcie_avst_up_eop(i)(2),
                p0_tx_st2_dvalid_i           => pcie_avst_up_dvalid(i)(2),

                p0_tx_st3_hdr_i              => pcie_avst_up_hdr(i)(512-1 downto 384),
                p0_tx_st3_prefix_i           => pcie_avst_up_prefix(i)(128-1 downto 96),
                p0_tx_st3_hvalid_i           => pcie_avst_up_hvalid(i)(3),
                p0_tx_st3_pvalid_i           => '0',
                p0_tx_st3_data_i             => pcie_avst_up_data(i)(1024-1 downto 768),
                p0_tx_st3_sop_i              => pcie_avst_up_sop(i)(3),
                p0_tx_st3_eop_i              => pcie_avst_up_eop(i)(3),
                p0_tx_st3_dvalid_i           => pcie_avst_up_dvalid(i)(3),

                p0_tx_st_hcrdt_init_o        => pcie_hcrdt_up_init(i),        --          p0_tx_st_misc.tx_st_Hcrdt_init
                p0_tx_st_hcrdt_update_o      => pcie_hcrdt_up_update(i),      --                       .tx_st_Hcrdt_update
                p0_tx_st_hcrdt_update_cnt_o  => pcie_hcrdt_up_update_cnt(i),  --                       .tx_st_Hcrdt_update_cnt
                p0_tx_st_hcrdt_init_ack_i    => pcie_hcrdt_up_init_ack(i),    --                       .tx_st_Hcrdtt_init_ack
                p0_tx_st_dcrdt_init_o        => pcie_dcrdt_up_init(i),        --                       .tx_st_Dcrdt_init
                p0_tx_st_dcrdt_update_o      => pcie_dcrdt_up_update(i),      --                       .tx_st_Dcrdt_update
                p0_tx_st_dcrdt_update_cnt_o  => pcie_dcrdt_up_update_cnt(i),  --                       .tx_st_Dcrdt_update_cnt
                p0_tx_st_dcrdt_init_ack_i    => pcie_dcrdt_up_init_ack(i),    --                       .tx_st_Dcrdt_init_ack

                p0_reset_status_n            => pcie_reset_status_n(i),            --      p0_reset_status_n.reset_n
                p0_slow_reset_status_n       => open,       -- p0_slow_reset_status_n.reset_n
                p0_link_up_o                 => pcie_link_up_comb(i),                 --          p0_hip_status.link_up
                p0_dl_up_o                   => open,                   --                       .dl_up
                p0_surprise_down_err_o       => open,       --                       .surprise_down_err
                p0_dl_timer_update_o         => open,         --                       .dl_timer_update
                p0_ltssm_state_delay_o       => open,       --                       .ltssm_state_delay
                p0_ltssm_st_hipfifo_ovrflw_o => open, --                       .ltssm_st_hipfifo_ovrflw
                p0_app_xfer_pending_i        => '0',        --          p0_power_mgnt.app_xfer_pending
                p0_pld_gp_status_i           => (others => '0'),           --              p0_pld_gp.status
                p0_pld_gp_ctrl_o             => open,             --                       .ctrl
                p0_pld_gp_status_ready_o     => open,     --                       .status_ready
                p0_cii_req_o                 => pcie_cii_req(i),                 --                 p0_cii.req
                p0_cii_hdr_poisoned_o        => pcie_cii_hdr_poisoned(i),        --                       .hdr_poisoned
                p0_cii_hdr_first_be_o        => pcie_cii_hdr_first_be(i),        --                       .hdr_first_be
                p0_cii_wr_o                  => pcie_cii_wr(i),                  --                       .wr
                p0_cii_addr_o                => pcie_cii_addr(i),                --                       .addr
                p0_cii_dout_o                => pcie_cii_dout(i),                --                       .dout
                p0_cii_override_en_i         => pcie_cii_override_en(i),         --                       .override_en
                p0_cii_override_din_i        => pcie_cii_override_din(i),        --                       .override_din
                p0_cii_halt_i                => pcie_cii_halt(i),                --                       .halt

                rx_n_in0                     => PCIE_RX_N(i*PCIE_LANES+0),                     --             hip_serial.rx_n_in0
                rx_n_in1                     => PCIE_RX_N(i*PCIE_LANES+1),                     --                       .rx_n_in1
                rx_n_in2                     => PCIE_RX_N(i*PCIE_LANES+2),                     --                       .rx_n_in2
                rx_n_in3                     => PCIE_RX_N(i*PCIE_LANES+3),                     --                       .rx_n_in3
                rx_n_in4                     => PCIE_RX_N(i*PCIE_LANES+4),                     --                       .rx_n_in4
                rx_n_in5                     => PCIE_RX_N(i*PCIE_LANES+5),                     --                       .rx_n_in5
                rx_n_in6                     => PCIE_RX_N(i*PCIE_LANES+6),                     --                       .rx_n_in6
                rx_n_in7                     => PCIE_RX_N(i*PCIE_LANES+7),                     --                       .rx_n_in7
                rx_n_in8                     => PCIE_RX_N(i*PCIE_LANES+8),                     --                       .rx_n_in8
                rx_n_in9                     => PCIE_RX_N(i*PCIE_LANES+9),                     --                       .rx_n_in9
                rx_n_in10                    => PCIE_RX_N(i*PCIE_LANES+10),                    --                       .rx_n_in10
                rx_n_in11                    => PCIE_RX_N(i*PCIE_LANES+11),                    --                       .rx_n_in11
                rx_n_in12                    => PCIE_RX_N(i*PCIE_LANES+12),                    --                       .rx_n_in12
                rx_n_in13                    => PCIE_RX_N(i*PCIE_LANES+13),                    --                       .rx_n_in13
                rx_n_in14                    => PCIE_RX_N(i*PCIE_LANES+14),                    --                       .rx_n_in14
                rx_n_in15                    => PCIE_RX_N(i*PCIE_LANES+15),                    --                       .rx_n_in15
                rx_p_in0                     => PCIE_RX_P(i*PCIE_LANES+0),                     --                       .rx_p_in0
                rx_p_in1                     => PCIE_RX_P(i*PCIE_LANES+1),                     --                       .rx_p_in1
                rx_p_in2                     => PCIE_RX_P(i*PCIE_LANES+2),                     --                       .rx_p_in2
                rx_p_in3                     => PCIE_RX_P(i*PCIE_LANES+3),                     --                       .rx_p_in3
                rx_p_in4                     => PCIE_RX_P(i*PCIE_LANES+4),                     --                       .rx_p_in4
                rx_p_in5                     => PCIE_RX_P(i*PCIE_LANES+5),                     --                       .rx_p_in5
                rx_p_in6                     => PCIE_RX_P(i*PCIE_LANES+6),                     --                       .rx_p_in6
                rx_p_in7                     => PCIE_RX_P(i*PCIE_LANES+7),                     --                       .rx_p_in7
                rx_p_in8                     => PCIE_RX_P(i*PCIE_LANES+8),                     --                       .rx_p_in8
                rx_p_in9                     => PCIE_RX_P(i*PCIE_LANES+9),                     --                       .rx_p_in9
                rx_p_in10                    => PCIE_RX_P(i*PCIE_LANES+10),                    --                       .rx_p_in10
                rx_p_in11                    => PCIE_RX_P(i*PCIE_LANES+11),                    --                       .rx_p_in11
                rx_p_in12                    => PCIE_RX_P(i*PCIE_LANES+12),                    --                       .rx_p_in12
                rx_p_in13                    => PCIE_RX_P(i*PCIE_LANES+13),                    --                       .rx_p_in13
                rx_p_in14                    => PCIE_RX_P(i*PCIE_LANES+14),                    --                       .rx_p_in14
                rx_p_in15                    => PCIE_RX_P(i*PCIE_LANES+15),                    --                       .rx_p_in15
                tx_n_out0                    => PCIE_TX_N(i*PCIE_LANES+0),                    --                       .tx_n_out0
                tx_n_out1                    => PCIE_TX_N(i*PCIE_LANES+1),                    --                       .tx_n_out1
                tx_n_out2                    => PCIE_TX_N(i*PCIE_LANES+2),                    --                       .tx_n_out2
                tx_n_out3                    => PCIE_TX_N(i*PCIE_LANES+3),                    --                       .tx_n_out3
                tx_n_out4                    => PCIE_TX_N(i*PCIE_LANES+4),                    --                       .tx_n_out4
                tx_n_out5                    => PCIE_TX_N(i*PCIE_LANES+5),                    --                       .tx_n_out5
                tx_n_out6                    => PCIE_TX_N(i*PCIE_LANES+6),                    --                       .tx_n_out6
                tx_n_out7                    => PCIE_TX_N(i*PCIE_LANES+7),                    --                       .tx_n_out7
                tx_n_out8                    => PCIE_TX_N(i*PCIE_LANES+8),                    --                       .tx_n_out8
                tx_n_out9                    => PCIE_TX_N(i*PCIE_LANES+9),                    --                       .tx_n_out9
                tx_n_out10                   => PCIE_TX_N(i*PCIE_LANES+10),                   --                       .tx_n_out10
                tx_n_out11                   => PCIE_TX_N(i*PCIE_LANES+11),                   --                       .tx_n_out11
                tx_n_out12                   => PCIE_TX_N(i*PCIE_LANES+12),                   --                       .tx_n_out12
                tx_n_out13                   => PCIE_TX_N(i*PCIE_LANES+13),                   --                       .tx_n_out13
                tx_n_out14                   => PCIE_TX_N(i*PCIE_LANES+14),                   --                       .tx_n_out14
                tx_n_out15                   => PCIE_TX_N(i*PCIE_LANES+15),                   --                       .tx_n_out15
                tx_p_out0                    => PCIE_TX_P(i*PCIE_LANES+0),                    --                       .tx_p_out0
                tx_p_out1                    => PCIE_TX_P(i*PCIE_LANES+1),                    --                       .tx_p_out1
                tx_p_out2                    => PCIE_TX_P(i*PCIE_LANES+2),                    --                       .tx_p_out2
                tx_p_out3                    => PCIE_TX_P(i*PCIE_LANES+3),                    --                       .tx_p_out3
                tx_p_out4                    => PCIE_TX_P(i*PCIE_LANES+4),                    --                       .tx_p_out4
                tx_p_out5                    => PCIE_TX_P(i*PCIE_LANES+5),                    --                       .tx_p_out5
                tx_p_out6                    => PCIE_TX_P(i*PCIE_LANES+6),                    --                       .tx_p_out6
                tx_p_out7                    => PCIE_TX_P(i*PCIE_LANES+7),                    --                       .tx_p_out7
                tx_p_out8                    => PCIE_TX_P(i*PCIE_LANES+8),                    --                       .tx_p_out8
                tx_p_out9                    => PCIE_TX_P(i*PCIE_LANES+9),                    --                       .tx_p_out9
                tx_p_out10                   => PCIE_TX_P(i*PCIE_LANES+10),                   --                       .tx_p_out10
                tx_p_out11                   => PCIE_TX_P(i*PCIE_LANES+11),                   --                       .tx_p_out11
                tx_p_out12                   => PCIE_TX_P(i*PCIE_LANES+12),                   --                       .tx_p_out12
                tx_p_out13                   => PCIE_TX_P(i*PCIE_LANES+13),                   --                       .tx_p_out13
                tx_p_out14                   => PCIE_TX_P(i*PCIE_LANES+14),                   --                       .tx_p_out14
                tx_p_out15                   => PCIE_TX_P(i*PCIE_LANES+15),                   --                       .tx_p_out15

                refclk0                      => PCIE_SYSCLK_P(i*PCIE_CLKS),                      --                refclk0.clk
                refclk1                      => PCIE_SYSCLK_P(i*PCIE_CLKS+1),                      --                refclk1.clk
                coreclkout_hip               => pcie_hip_clk(i),               --         coreclkout_hip.clk
                ninit_done                   => pcie_init_done_n(i),                   --             ninit_done.ninit_done
                slow_clk                     => pcie_hip_slow_clk(i),                    --               slow_clk.clk
                pin_perst_n                  => PCIE_SYSRST_N(i),                  --              pin_perst.pin_perst
                pin_perst_n_o                => open
            );

            pcie_clk(i)         <= pcie_hip_clk(i);
            pcie_slow_clk(i)    <= pcie_hip_slow_clk(i);
            pcie_init_done_n(i) <= INIT_DONE_N;
        end generate;
    end generate;

    -- =========================================================================
    --  UP/DOWN AVALON-ST INTERFACE
    -- =========================================================================

    pcie_adapter_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        --TODO insert pcie function to HDR
    
        -- Global valid created as OR data and header valids
        pcie_avst_down_valid(i) <= pcie_avst_down_dvalid(i) or pcie_avst_down_hvalid(i);

        process (pcie_clk(i))
        begin
            if (rising_edge(pcie_clk(i))) then
                pcie_avst_up_payload_lv(i)(0) <= pcie_avst_up_payload_lv(i)(CC_MFB_REGIONS);
            end if;
        end process;

        pcie_avst_g : for r in 0 to CC_MFB_REGIONS-1 generate
            process (all)
            begin
                if (pcie_avst_up_valid(i)(r) = '1' and pcie_avst_up_sop(i)(r) = '1') then
                    -- Valid for transaction data, second bit of Fmt field in PCIe
                    -- header (native format) indicates a data transaction.
                    pcie_avst_up_payload_lv(i)(r+1) <= pcie_avst_up_hdr(i)(r*128+126);
                else
                    pcie_avst_up_payload_lv(i)(r+1) <= pcie_avst_up_payload_lv(i)(r);
                end if;
            end process;

            pcie_avst_up_dvalid(i)(r) <= pcie_avst_up_valid(i)(r) and pcie_avst_up_payload_lv(i)(r+1);
        end generate;
        -- Valid for transaction header, valid only with SOP
        pcie_avst_up_hvalid(i) <= pcie_avst_up_valid(i) and pcie_avst_up_sop(i);

        -- PCIe Header Format must be Enabled in R-Tile!
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
            ENDPOINT_TYPE      => "R_TILE",
            DEVICE             => DEVICE,
            CQ_FIFO_ITEMS      => CQ_FIFO_ITEMS,
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
    
            CRDT_DOWN_INIT_DONE => crdt_down_init_done(i),
            CRDT_DOWN_UPDATE    => crdt_down_update(i),
            CRDT_DOWN_CNT_PH    => crdt_down_cnt_ph(i),
            CRDT_DOWN_CNT_NPH   => crdt_down_cnt_nph(i),
            CRDT_DOWN_CNT_CPLH  => crdt_down_cnt_cplh(i),
            CRDT_DOWN_CNT_PD    => crdt_down_cnt_pd(i),
            CRDT_DOWN_CNT_NPD   => crdt_down_cnt_npd(i),
            CRDT_DOWN_CNT_CPLD  => crdt_down_cnt_cpld(i),
    
            CRDT_UP_INIT_DONE   => crdt_up_init_done(i),
            CRDT_UP_UPDATE      => crdt_up_update(i),
            CRDT_UP_CNT_PH      => crdt_up_cnt_ph(i),
            CRDT_UP_CNT_NPH     => crdt_up_cnt_nph(i),
            CRDT_UP_CNT_CPLH    => crdt_up_cnt_cplh(i),
            CRDT_UP_CNT_PD      => crdt_up_cnt_pd(i),
            CRDT_UP_CNT_NPD     => crdt_up_cnt_npd(i),
            CRDT_UP_CNT_CPLD    => crdt_up_cnt_cpld(i),
    
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

    -- =========================================================================
    --  UP/DOWN CREDIT FLOW CONTROL INTERFACE LOGIC
    -- =========================================================================

    crdt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        crdt_i : entity work.PCIE_CRDT_LOGIC
        generic map (
            CRDT_TOTAL_PH   => CRDT_TOTAL_XPH/2,
            CRDT_TOTAL_NPH  => CRDT_TOTAL_XPH/2,
            CRDT_TOTAL_CPLH => 0,
            CRDT_TOTAL_PD   => MTC_FIFO_CRDT/2,
            CRDT_TOTAL_NPD  => MTC_FIFO_CRDT/2,
            CRDT_TOTAL_CPLD => 0
        )
        port map (
            CLK                      => pcie_clk(i),
            RESET                    => pcie_rst(i)(0),

            PCIE_HCRDT_UP_INIT       => pcie_hcrdt_up_init(i),
            PCIE_HCRDT_UP_INIT_ACK   => pcie_hcrdt_up_init_ack(i),
            PCIE_HCRDT_UP_UPDATE     => pcie_hcrdt_up_update(i),
            PCIE_HCRDT_UP_UPDATE_CNT => pcie_hcrdt_up_update_cnt(i),
            PCIE_DCRDT_UP_INIT       => pcie_dcrdt_up_init(i),
            PCIE_DCRDT_UP_INIT_ACK   => pcie_dcrdt_up_init_ack(i),
            PCIE_DCRDT_UP_UPDATE     => pcie_dcrdt_up_update(i),
            PCIE_DCRDT_UP_UPDATE_CNT => pcie_dcrdt_up_update_cnt(i),
        
            PCIE_HCRDT_DW_INIT       => pcie_hcrdt_dw_init(i),
            PCIE_HCRDT_DW_INIT_ACK   => pcie_hcrdt_dw_init_ack(i),
            PCIE_HCRDT_DW_UPDATE     => pcie_hcrdt_dw_update(i),
            PCIE_HCRDT_DW_UPDATE_CNT => pcie_hcrdt_dw_update_cnt(i),
            PCIE_DCRDT_DW_INIT       => pcie_dcrdt_dw_init(i),
            PCIE_DCRDT_DW_INIT_ACK   => pcie_dcrdt_dw_init_ack(i),
            PCIE_DCRDT_DW_UPDATE     => pcie_dcrdt_dw_update(i),
            PCIE_DCRDT_DW_UPDATE_CNT => pcie_dcrdt_dw_update_cnt(i),

            CRDT_UP_INIT_DONE        => crdt_up_init_done(i),
            CRDT_UP_UPDATE           => crdt_up_update(i),
            CRDT_UP_CNT_PH           => crdt_up_cnt_ph(i),
            CRDT_UP_CNT_NPH          => crdt_up_cnt_nph(i),
            CRDT_UP_CNT_CPLH         => crdt_up_cnt_cplh(i),
            CRDT_UP_CNT_PD           => crdt_up_cnt_pd(i),
            CRDT_UP_CNT_NPD          => crdt_up_cnt_npd(i),
            CRDT_UP_CNT_CPLD         => crdt_up_cnt_cpld(i),

            CRDT_DOWN_INIT_DONE      => crdt_down_init_done(i),
            CRDT_DOWN_UPDATE         => crdt_down_update(i),
            CRDT_DOWN_CNT_PH         => crdt_down_cnt_ph(i),
            CRDT_DOWN_CNT_NPH        => crdt_down_cnt_nph(i),
            CRDT_DOWN_CNT_CPLH       => crdt_down_cnt_cplh(i),
            CRDT_DOWN_CNT_PD         => crdt_down_cnt_pd(i),
            CRDT_DOWN_CNT_NPD        => crdt_down_cnt_npd(i),
            CRDT_DOWN_CNT_CPLD       => crdt_down_cnt_cpld(i)
        );
    end generate;

    -- =========================================================================
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_reset_status <= not pcie_reset_status_n;

    pcie_rst_g : for i in 0 to PCIE_ENDPOINTS-1 generate
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

        pcie_slow_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => 1
        )
        port map (
            CLK        => pcie_slow_clk(i),
            ASYNC_RST  => pcie_reset_status(i),
            OUT_RST(0) => pcie_slow_rst(i)
        );

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

        --TODO
        PCIE_MPS(i)            <= "001"; -- 256B
        PCIE_MRRS(i)           <= "010"; -- 512B
        PCIE_EXT_TAG_EN(i)     <= '1';
        PCIE_RCB_SIZE(i)       <= '0';
        PCIE_10B_TAG_REQ_EN(i) <= '0';
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        constant dt_en : boolean := (i = 0);
    begin
        cii2cfg_ext_i: entity work.PCIE_CII2CFG_EXT
        port map(
            CLK                    => pcie_slow_clk(i),
            RESET                  => pcie_slow_rst(i),

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
            CLK                    => pcie_slow_clk(i),
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

end architecture;
