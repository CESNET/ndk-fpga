-- pcie_core_htile.vhd: PCIe module
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Denis Kurka <xkurka05@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

architecture HTILE of PCIE_CORE is

    component htile_pcie_1x16 is
        port (
            refclk                    : in  std_logic                      := 'X';             -- clk
            coreclkout_hip            : out std_logic;                                         -- clk
            npor                      : in  std_logic                      := 'X';             -- npor
            pin_perst                 : in  std_logic                      := 'X';             -- pin_perst
            reset_status              : out std_logic;                                         -- reset_status
            serdes_pll_locked         : out std_logic;                                         -- serdes_pll_locked
            pld_core_ready            : in  std_logic                      := 'X';             -- pld_core_ready
            pld_clk_inuse             : out std_logic;                                         -- pld_clk_inuse
            testin_zero               : out std_logic;                                         -- testin_zero
            clr_st                    : out std_logic;                                         -- reset
            ninit_done                : in  std_logic                      := 'X';             -- ninit_done
            rx_st_ready               : in  std_logic                      := 'X';             -- ready
            rx_st_sop                 : out std_logic_vector(1 downto 0);                      -- startofpacket
            rx_st_eop                 : out std_logic_vector(1 downto 0);                      -- endofpacket
            rx_st_data                : out std_logic_vector(511 downto 0);                    -- data
            rx_st_valid               : out std_logic_vector(1 downto 0);                      -- valid
            rx_st_empty               : out std_logic_vector(5 downto 0);                      -- empty
            tx_st_sop                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- startofpacket
            tx_st_eop                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- endofpacket
            tx_st_data                : in  std_logic_vector(511 downto 0) := (others => 'X'); -- data
            tx_st_valid               : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- valid
            tx_st_err                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- error
            tx_st_ready               : out std_logic;                                         -- ready
            rx_st_bar_range           : out std_logic_vector(5 downto 0);                      -- rx_st_bar_range
            tx_cdts_type              : out std_logic_vector(3 downto 0);                      -- tx_cdts_type
            tx_data_cdts_consumed     : out std_logic_vector(1 downto 0);                      -- tx_data_cdts_consumed
            tx_hdr_cdts_consumed      : out std_logic_vector(1 downto 0);                      -- tx_hdr_cdts_consumed
            tx_cdts_data_value        : out std_logic_vector(1 downto 0);                      -- tx_cdts_data_value
            tx_cpld_cdts              : out std_logic_vector(11 downto 0);                     -- tx_cpld_cdts
            tx_pd_cdts                : out std_logic_vector(11 downto 0);                     -- tx_pd_cdts
            tx_npd_cdts               : out std_logic_vector(11 downto 0);                     -- tx_npd_cdts
            tx_cplh_cdts              : out std_logic_vector(7 downto 0);                      -- tx_cplh_cdts
            tx_ph_cdts                : out std_logic_vector(7 downto 0);                      -- tx_ph_cdts
            tx_nph_cdts               : out std_logic_vector(7 downto 0);                      -- tx_nph_cdts
            app_msi_req               : in  std_logic                      := 'X';             -- app_msi_req
            app_msi_ack               : out std_logic;                                         -- app_msi_ack
            app_msi_tc                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- app_msi_tc
            app_msi_num               : in  std_logic_vector(4 downto 0)   := (others => 'X'); -- app_msi_num
            app_int_sts               : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- app_int_sts
            app_msi_func_num          : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- app_msi_func_num
            int_status                : out std_logic_vector(10 downto 0);                     -- int_status
            int_status_common         : out std_logic_vector(2 downto 0);                      -- int_status_common
            derr_cor_ext_rpl          : out std_logic;                                         -- derr_cor_ext_rpl
            derr_rpl                  : out std_logic;                                         -- derr_rpl
            derr_cor_ext_rcv          : out std_logic;                                         -- derr_cor_ext_rcv
            derr_uncor_ext_rcv        : out std_logic;                                         -- derr_uncor_ext_rcv
            rx_par_err                : out std_logic;                                         -- rx_par_err
            tx_par_err                : out std_logic;                                         -- tx_par_err
            ltssmstate                : out std_logic_vector(5 downto 0);                      -- ltssmstate
            link_up                   : out std_logic;                                         -- link_up
            lane_act                  : out std_logic_vector(4 downto 0);                      -- lane_act
            --flr_pf_done               : in  std_logic                      := 'X';             -- flr_pf_done
            --flr_pf_active             : out std_logic;                                         -- flr_pf_active
            tl_cfg_func               : out std_logic_vector(1 downto 0);                      -- tl_cfg_func
            tl_cfg_add                : out std_logic_vector(3 downto 0);                      -- tl_cfg_add
            tl_cfg_ctl                : out std_logic_vector(31 downto 0);                     -- tl_cfg_ctl
            app_err_valid             : in  std_logic                      := 'X';             -- app_err_valid
            app_err_hdr               : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- app_err_hdr
            app_err_info              : in  std_logic_vector(10 downto 0)  := (others => 'X'); -- app_err_info
            app_err_func_num          : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- app_err_func_num
            test_in                   : in  std_logic_vector(66 downto 0)  := (others => 'X'); -- test_in
            simu_mode_pipe            : in  std_logic                      := 'X';             -- simu_mode_pipe
            currentspeed              : out std_logic_vector(1 downto 0);                      -- currentspeed
            ceb_ack                   : in  std_logic                      := 'X';             -- ceb_ack
            ceb_din                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- ceb_din
            ceb_addr                  : out std_logic_vector(11 downto 0);                     -- ceb_addr
            ceb_req                   : out std_logic;                                         -- ceb_req
            ceb_dout                  : out std_logic_vector(31 downto 0);                     -- ceb_dout
            ceb_wr                    : out std_logic_vector(3 downto 0);                      -- ceb_wr
            ceb_cdm_convert_data      : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- ceb_cdm_convert_data
            ceb_func_num              : out std_logic_vector(1 downto 0);                      -- ceb_func_num
            sim_pipe_pclk_in          : in  std_logic                      := 'X';             -- sim_pipe_pclk_in
            sim_pipe_rate             : out std_logic_vector(1 downto 0);                      -- sim_pipe_rate
            sim_ltssmstate            : out std_logic_vector(5 downto 0);                      -- sim_ltssmstate
            txdata0                   : out std_logic_vector(31 downto 0);                     -- txdata0
            txdata1                   : out std_logic_vector(31 downto 0);                     -- txdata1
            txdata2                   : out std_logic_vector(31 downto 0);                     -- txdata2
            txdata3                   : out std_logic_vector(31 downto 0);                     -- txdata3
            txdata4                   : out std_logic_vector(31 downto 0);                     -- txdata4
            txdata5                   : out std_logic_vector(31 downto 0);                     -- txdata5
            txdata6                   : out std_logic_vector(31 downto 0);                     -- txdata6
            txdata7                   : out std_logic_vector(31 downto 0);                     -- txdata7
            txdata8                   : out std_logic_vector(31 downto 0);                     -- txdata8
            txdata9                   : out std_logic_vector(31 downto 0);                     -- txdata9
            txdata10                  : out std_logic_vector(31 downto 0);                     -- txdata10
            txdata11                  : out std_logic_vector(31 downto 0);                     -- txdata11
            txdata12                  : out std_logic_vector(31 downto 0);                     -- txdata12
            txdata13                  : out std_logic_vector(31 downto 0);                     -- txdata13
            txdata14                  : out std_logic_vector(31 downto 0);                     -- txdata14
            txdata15                  : out std_logic_vector(31 downto 0);                     -- txdata15
            txdatak0                  : out std_logic_vector(3 downto 0);                      -- txdatak0
            txdatak1                  : out std_logic_vector(3 downto 0);                      -- txdatak1
            txdatak2                  : out std_logic_vector(3 downto 0);                      -- txdatak2
            txdatak3                  : out std_logic_vector(3 downto 0);                      -- txdatak3
            txdatak4                  : out std_logic_vector(3 downto 0);                      -- txdatak4
            txdatak5                  : out std_logic_vector(3 downto 0);                      -- txdatak5
            txdatak6                  : out std_logic_vector(3 downto 0);                      -- txdatak6
            txdatak7                  : out std_logic_vector(3 downto 0);                      -- txdatak7
            txdatak8                  : out std_logic_vector(3 downto 0);                      -- txdatak8
            txdatak9                  : out std_logic_vector(3 downto 0);                      -- txdatak9
            txdatak10                 : out std_logic_vector(3 downto 0);                      -- txdatak10
            txdatak11                 : out std_logic_vector(3 downto 0);                      -- txdatak11
            txdatak12                 : out std_logic_vector(3 downto 0);                      -- txdatak12
            txdatak13                 : out std_logic_vector(3 downto 0);                      -- txdatak13
            txdatak14                 : out std_logic_vector(3 downto 0);                      -- txdatak14
            txdatak15                 : out std_logic_vector(3 downto 0);                      -- txdatak15
            txcompl0                  : out std_logic;                                         -- txcompl0
            txcompl1                  : out std_logic;                                         -- txcompl1
            txcompl2                  : out std_logic;                                         -- txcompl2
            txcompl3                  : out std_logic;                                         -- txcompl3
            txcompl4                  : out std_logic;                                         -- txcompl4
            txcompl5                  : out std_logic;                                         -- txcompl5
            txcompl6                  : out std_logic;                                         -- txcompl6
            txcompl7                  : out std_logic;                                         -- txcompl7
            txcompl8                  : out std_logic;                                         -- txcompl8
            txcompl9                  : out std_logic;                                         -- txcompl9
            txcompl10                 : out std_logic;                                         -- txcompl10
            txcompl11                 : out std_logic;                                         -- txcompl11
            txcompl12                 : out std_logic;                                         -- txcompl12
            txcompl13                 : out std_logic;                                         -- txcompl13
            txcompl14                 : out std_logic;                                         -- txcompl14
            txcompl15                 : out std_logic;                                         -- txcompl15
            txelecidle0               : out std_logic;                                         -- txelecidle0
            txelecidle1               : out std_logic;                                         -- txelecidle1
            txelecidle2               : out std_logic;                                         -- txelecidle2
            txelecidle3               : out std_logic;                                         -- txelecidle3
            txelecidle4               : out std_logic;                                         -- txelecidle4
            txelecidle5               : out std_logic;                                         -- txelecidle5
            txelecidle6               : out std_logic;                                         -- txelecidle6
            txelecidle7               : out std_logic;                                         -- txelecidle7
            txelecidle8               : out std_logic;                                         -- txelecidle8
            txelecidle9               : out std_logic;                                         -- txelecidle9
            txelecidle10              : out std_logic;                                         -- txelecidle10
            txelecidle11              : out std_logic;                                         -- txelecidle11
            txelecidle12              : out std_logic;                                         -- txelecidle12
            txelecidle13              : out std_logic;                                         -- txelecidle13
            txelecidle14              : out std_logic;                                         -- txelecidle14
            txelecidle15              : out std_logic;                                         -- txelecidle15
            txdetectrx0               : out std_logic;                                         -- txdetectrx0
            txdetectrx1               : out std_logic;                                         -- txdetectrx1
            txdetectrx2               : out std_logic;                                         -- txdetectrx2
            txdetectrx3               : out std_logic;                                         -- txdetectrx3
            txdetectrx4               : out std_logic;                                         -- txdetectrx4
            txdetectrx5               : out std_logic;                                         -- txdetectrx5
            txdetectrx6               : out std_logic;                                         -- txdetectrx6
            txdetectrx7               : out std_logic;                                         -- txdetectrx7
            txdetectrx8               : out std_logic;                                         -- txdetectrx8
            txdetectrx9               : out std_logic;                                         -- txdetectrx9
            txdetectrx10              : out std_logic;                                         -- txdetectrx10
            txdetectrx11              : out std_logic;                                         -- txdetectrx11
            txdetectrx12              : out std_logic;                                         -- txdetectrx12
            txdetectrx13              : out std_logic;                                         -- txdetectrx13
            txdetectrx14              : out std_logic;                                         -- txdetectrx14
            txdetectrx15              : out std_logic;                                         -- txdetectrx15
            powerdown0                : out std_logic_vector(1 downto 0);                      -- powerdown0
            powerdown1                : out std_logic_vector(1 downto 0);                      -- powerdown1
            powerdown2                : out std_logic_vector(1 downto 0);                      -- powerdown2
            powerdown3                : out std_logic_vector(1 downto 0);                      -- powerdown3
            powerdown4                : out std_logic_vector(1 downto 0);                      -- powerdown4
            powerdown5                : out std_logic_vector(1 downto 0);                      -- powerdown5
            powerdown6                : out std_logic_vector(1 downto 0);                      -- powerdown6
            powerdown7                : out std_logic_vector(1 downto 0);                      -- powerdown7
            powerdown8                : out std_logic_vector(1 downto 0);                      -- powerdown8
            powerdown9                : out std_logic_vector(1 downto 0);                      -- powerdown9
            powerdown10               : out std_logic_vector(1 downto 0);                      -- powerdown10
            powerdown11               : out std_logic_vector(1 downto 0);                      -- powerdown11
            powerdown12               : out std_logic_vector(1 downto 0);                      -- powerdown12
            powerdown13               : out std_logic_vector(1 downto 0);                      -- powerdown13
            powerdown14               : out std_logic_vector(1 downto 0);                      -- powerdown14
            powerdown15               : out std_logic_vector(1 downto 0);                      -- powerdown15
            txmargin0                 : out std_logic_vector(2 downto 0);                      -- txmargin0
            txmargin1                 : out std_logic_vector(2 downto 0);                      -- txmargin1
            txmargin2                 : out std_logic_vector(2 downto 0);                      -- txmargin2
            txmargin3                 : out std_logic_vector(2 downto 0);                      -- txmargin3
            txmargin4                 : out std_logic_vector(2 downto 0);                      -- txmargin4
            txmargin5                 : out std_logic_vector(2 downto 0);                      -- txmargin5
            txmargin6                 : out std_logic_vector(2 downto 0);                      -- txmargin6
            txmargin7                 : out std_logic_vector(2 downto 0);                      -- txmargin7
            txmargin8                 : out std_logic_vector(2 downto 0);                      -- txmargin8
            txmargin9                 : out std_logic_vector(2 downto 0);                      -- txmargin9
            txmargin10                : out std_logic_vector(2 downto 0);                      -- txmargin10
            txmargin11                : out std_logic_vector(2 downto 0);                      -- txmargin11
            txmargin12                : out std_logic_vector(2 downto 0);                      -- txmargin12
            txmargin13                : out std_logic_vector(2 downto 0);                      -- txmargin13
            txmargin14                : out std_logic_vector(2 downto 0);                      -- txmargin14
            txmargin15                : out std_logic_vector(2 downto 0);                      -- txmargin15
            txdeemph0                 : out std_logic;                                         -- txdeemph0
            txdeemph1                 : out std_logic;                                         -- txdeemph1
            txdeemph2                 : out std_logic;                                         -- txdeemph2
            txdeemph3                 : out std_logic;                                         -- txdeemph3
            txdeemph4                 : out std_logic;                                         -- txdeemph4
            txdeemph5                 : out std_logic;                                         -- txdeemph5
            txdeemph6                 : out std_logic;                                         -- txdeemph6
            txdeemph7                 : out std_logic;                                         -- txdeemph7
            txdeemph8                 : out std_logic;                                         -- txdeemph8
            txdeemph9                 : out std_logic;                                         -- txdeemph9
            txdeemph10                : out std_logic;                                         -- txdeemph10
            txdeemph11                : out std_logic;                                         -- txdeemph11
            txdeemph12                : out std_logic;                                         -- txdeemph12
            txdeemph13                : out std_logic;                                         -- txdeemph13
            txdeemph14                : out std_logic;                                         -- txdeemph14
            txdeemph15                : out std_logic;                                         -- txdeemph15
            txswing0                  : out std_logic;                                         -- txswing0
            txswing1                  : out std_logic;                                         -- txswing1
            txswing2                  : out std_logic;                                         -- txswing2
            txswing3                  : out std_logic;                                         -- txswing3
            txswing4                  : out std_logic;                                         -- txswing4
            txswing5                  : out std_logic;                                         -- txswing5
            txswing6                  : out std_logic;                                         -- txswing6
            txswing7                  : out std_logic;                                         -- txswing7
            txswing8                  : out std_logic;                                         -- txswing8
            txswing9                  : out std_logic;                                         -- txswing9
            txswing10                 : out std_logic;                                         -- txswing10
            txswing11                 : out std_logic;                                         -- txswing11
            txswing12                 : out std_logic;                                         -- txswing12
            txswing13                 : out std_logic;                                         -- txswing13
            txswing14                 : out std_logic;                                         -- txswing14
            txswing15                 : out std_logic;                                         -- txswing15
            txsynchd0                 : out std_logic_vector(1 downto 0);                      -- txsynchd0
            txsynchd1                 : out std_logic_vector(1 downto 0);                      -- txsynchd1
            txsynchd2                 : out std_logic_vector(1 downto 0);                      -- txsynchd2
            txsynchd3                 : out std_logic_vector(1 downto 0);                      -- txsynchd3
            txsynchd4                 : out std_logic_vector(1 downto 0);                      -- txsynchd4
            txsynchd5                 : out std_logic_vector(1 downto 0);                      -- txsynchd5
            txsynchd6                 : out std_logic_vector(1 downto 0);                      -- txsynchd6
            txsynchd7                 : out std_logic_vector(1 downto 0);                      -- txsynchd7
            txsynchd8                 : out std_logic_vector(1 downto 0);                      -- txsynchd8
            txsynchd9                 : out std_logic_vector(1 downto 0);                      -- txsynchd9
            txsynchd10                : out std_logic_vector(1 downto 0);                      -- txsynchd10
            txsynchd11                : out std_logic_vector(1 downto 0);                      -- txsynchd11
            txsynchd12                : out std_logic_vector(1 downto 0);                      -- txsynchd12
            txsynchd13                : out std_logic_vector(1 downto 0);                      -- txsynchd13
            txsynchd14                : out std_logic_vector(1 downto 0);                      -- txsynchd14
            txsynchd15                : out std_logic_vector(1 downto 0);                      -- txsynchd15
            txblkst0                  : out std_logic;                                         -- txblkst0
            txblkst1                  : out std_logic;                                         -- txblkst1
            txblkst2                  : out std_logic;                                         -- txblkst2
            txblkst3                  : out std_logic;                                         -- txblkst3
            txblkst4                  : out std_logic;                                         -- txblkst4
            txblkst5                  : out std_logic;                                         -- txblkst5
            txblkst6                  : out std_logic;                                         -- txblkst6
            txblkst7                  : out std_logic;                                         -- txblkst7
            txblkst8                  : out std_logic;                                         -- txblkst8
            txblkst9                  : out std_logic;                                         -- txblkst9
            txblkst10                 : out std_logic;                                         -- txblkst10
            txblkst11                 : out std_logic;                                         -- txblkst11
            txblkst12                 : out std_logic;                                         -- txblkst12
            txblkst13                 : out std_logic;                                         -- txblkst13
            txblkst14                 : out std_logic;                                         -- txblkst14
            txblkst15                 : out std_logic;                                         -- txblkst15
            txdataskip0               : out std_logic;                                         -- txdataskip0
            txdataskip1               : out std_logic;                                         -- txdataskip1
            txdataskip2               : out std_logic;                                         -- txdataskip2
            txdataskip3               : out std_logic;                                         -- txdataskip3
            txdataskip4               : out std_logic;                                         -- txdataskip4
            txdataskip5               : out std_logic;                                         -- txdataskip5
            txdataskip6               : out std_logic;                                         -- txdataskip6
            txdataskip7               : out std_logic;                                         -- txdataskip7
            txdataskip8               : out std_logic;                                         -- txdataskip8
            txdataskip9               : out std_logic;                                         -- txdataskip9
            txdataskip10              : out std_logic;                                         -- txdataskip10
            txdataskip11              : out std_logic;                                         -- txdataskip11
            txdataskip12              : out std_logic;                                         -- txdataskip12
            txdataskip13              : out std_logic;                                         -- txdataskip13
            txdataskip14              : out std_logic;                                         -- txdataskip14
            txdataskip15              : out std_logic;                                         -- txdataskip15
            rate0                     : out std_logic_vector(1 downto 0);                      -- rate0
            rate1                     : out std_logic_vector(1 downto 0);                      -- rate1
            rate2                     : out std_logic_vector(1 downto 0);                      -- rate2
            rate3                     : out std_logic_vector(1 downto 0);                      -- rate3
            rate4                     : out std_logic_vector(1 downto 0);                      -- rate4
            rate5                     : out std_logic_vector(1 downto 0);                      -- rate5
            rate6                     : out std_logic_vector(1 downto 0);                      -- rate6
            rate7                     : out std_logic_vector(1 downto 0);                      -- rate7
            rate8                     : out std_logic_vector(1 downto 0);                      -- rate8
            rate9                     : out std_logic_vector(1 downto 0);                      -- rate9
            rate10                    : out std_logic_vector(1 downto 0);                      -- rate10
            rate11                    : out std_logic_vector(1 downto 0);                      -- rate11
            rate12                    : out std_logic_vector(1 downto 0);                      -- rate12
            rate13                    : out std_logic_vector(1 downto 0);                      -- rate13
            rate14                    : out std_logic_vector(1 downto 0);                      -- rate14
            rate15                    : out std_logic_vector(1 downto 0);                      -- rate15
            rxpolarity0               : out std_logic;                                         -- rxpolarity0
            rxpolarity1               : out std_logic;                                         -- rxpolarity1
            rxpolarity2               : out std_logic;                                         -- rxpolarity2
            rxpolarity3               : out std_logic;                                         -- rxpolarity3
            rxpolarity4               : out std_logic;                                         -- rxpolarity4
            rxpolarity5               : out std_logic;                                         -- rxpolarity5
            rxpolarity6               : out std_logic;                                         -- rxpolarity6
            rxpolarity7               : out std_logic;                                         -- rxpolarity7
            rxpolarity8               : out std_logic;                                         -- rxpolarity8
            rxpolarity9               : out std_logic;                                         -- rxpolarity9
            rxpolarity10              : out std_logic;                                         -- rxpolarity10
            rxpolarity11              : out std_logic;                                         -- rxpolarity11
            rxpolarity12              : out std_logic;                                         -- rxpolarity12
            rxpolarity13              : out std_logic;                                         -- rxpolarity13
            rxpolarity14              : out std_logic;                                         -- rxpolarity14
            rxpolarity15              : out std_logic;                                         -- rxpolarity15
            currentrxpreset0          : out std_logic_vector(2 downto 0);                      -- currentrxpreset0
            currentrxpreset1          : out std_logic_vector(2 downto 0);                      -- currentrxpreset1
            currentrxpreset2          : out std_logic_vector(2 downto 0);                      -- currentrxpreset2
            currentrxpreset3          : out std_logic_vector(2 downto 0);                      -- currentrxpreset3
            currentrxpreset4          : out std_logic_vector(2 downto 0);                      -- currentrxpreset4
            currentrxpreset5          : out std_logic_vector(2 downto 0);                      -- currentrxpreset5
            currentrxpreset6          : out std_logic_vector(2 downto 0);                      -- currentrxpreset6
            currentrxpreset7          : out std_logic_vector(2 downto 0);                      -- currentrxpreset7
            currentrxpreset8          : out std_logic_vector(2 downto 0);                      -- currentrxpreset8
            currentrxpreset9          : out std_logic_vector(2 downto 0);                      -- currentrxpreset9
            currentrxpreset10         : out std_logic_vector(2 downto 0);                      -- currentrxpreset10
            currentrxpreset11         : out std_logic_vector(2 downto 0);                      -- currentrxpreset11
            currentrxpreset12         : out std_logic_vector(2 downto 0);                      -- currentrxpreset12
            currentrxpreset13         : out std_logic_vector(2 downto 0);                      -- currentrxpreset13
            currentrxpreset14         : out std_logic_vector(2 downto 0);                      -- currentrxpreset14
            currentrxpreset15         : out std_logic_vector(2 downto 0);                      -- currentrxpreset15
            currentcoeff0             : out std_logic_vector(17 downto 0);                     -- currentcoeff0
            currentcoeff1             : out std_logic_vector(17 downto 0);                     -- currentcoeff1
            currentcoeff2             : out std_logic_vector(17 downto 0);                     -- currentcoeff2
            currentcoeff3             : out std_logic_vector(17 downto 0);                     -- currentcoeff3
            currentcoeff4             : out std_logic_vector(17 downto 0);                     -- currentcoeff4
            currentcoeff5             : out std_logic_vector(17 downto 0);                     -- currentcoeff5
            currentcoeff6             : out std_logic_vector(17 downto 0);                     -- currentcoeff6
            currentcoeff7             : out std_logic_vector(17 downto 0);                     -- currentcoeff7
            currentcoeff8             : out std_logic_vector(17 downto 0);                     -- currentcoeff8
            currentcoeff9             : out std_logic_vector(17 downto 0);                     -- currentcoeff9
            currentcoeff10            : out std_logic_vector(17 downto 0);                     -- currentcoeff10
            currentcoeff11            : out std_logic_vector(17 downto 0);                     -- currentcoeff11
            currentcoeff12            : out std_logic_vector(17 downto 0);                     -- currentcoeff12
            currentcoeff13            : out std_logic_vector(17 downto 0);                     -- currentcoeff13
            currentcoeff14            : out std_logic_vector(17 downto 0);                     -- currentcoeff14
            currentcoeff15            : out std_logic_vector(17 downto 0);                     -- currentcoeff15
            rxeqeval0                 : out std_logic;                                         -- rxeqeval0
            rxeqeval1                 : out std_logic;                                         -- rxeqeval1
            rxeqeval2                 : out std_logic;                                         -- rxeqeval2
            rxeqeval3                 : out std_logic;                                         -- rxeqeval3
            rxeqeval4                 : out std_logic;                                         -- rxeqeval4
            rxeqeval5                 : out std_logic;                                         -- rxeqeval5
            rxeqeval6                 : out std_logic;                                         -- rxeqeval6
            rxeqeval7                 : out std_logic;                                         -- rxeqeval7
            rxeqeval8                 : out std_logic;                                         -- rxeqeval8
            rxeqeval9                 : out std_logic;                                         -- rxeqeval9
            rxeqeval10                : out std_logic;                                         -- rxeqeval10
            rxeqeval11                : out std_logic;                                         -- rxeqeval11
            rxeqeval12                : out std_logic;                                         -- rxeqeval12
            rxeqeval13                : out std_logic;                                         -- rxeqeval13
            rxeqeval14                : out std_logic;                                         -- rxeqeval14
            rxeqeval15                : out std_logic;                                         -- rxeqeval15
            rxeqinprogress0           : out std_logic;                                         -- rxeqinprogress0
            rxeqinprogress1           : out std_logic;                                         -- rxeqinprogress1
            rxeqinprogress2           : out std_logic;                                         -- rxeqinprogress2
            rxeqinprogress3           : out std_logic;                                         -- rxeqinprogress3
            rxeqinprogress4           : out std_logic;                                         -- rxeqinprogress4
            rxeqinprogress5           : out std_logic;                                         -- rxeqinprogress5
            rxeqinprogress6           : out std_logic;                                         -- rxeqinprogress6
            rxeqinprogress7           : out std_logic;                                         -- rxeqinprogress7
            rxeqinprogress8           : out std_logic;                                         -- rxeqinprogress8
            rxeqinprogress9           : out std_logic;                                         -- rxeqinprogress9
            rxeqinprogress10          : out std_logic;                                         -- rxeqinprogress10
            rxeqinprogress11          : out std_logic;                                         -- rxeqinprogress11
            rxeqinprogress12          : out std_logic;                                         -- rxeqinprogress12
            rxeqinprogress13          : out std_logic;                                         -- rxeqinprogress13
            rxeqinprogress14          : out std_logic;                                         -- rxeqinprogress14
            rxeqinprogress15          : out std_logic;                                         -- rxeqinprogress15
            invalidreq0               : out std_logic;                                         -- invalidreq0
            invalidreq1               : out std_logic;                                         -- invalidreq1
            invalidreq2               : out std_logic;                                         -- invalidreq2
            invalidreq3               : out std_logic;                                         -- invalidreq3
            invalidreq4               : out std_logic;                                         -- invalidreq4
            invalidreq5               : out std_logic;                                         -- invalidreq5
            invalidreq6               : out std_logic;                                         -- invalidreq6
            invalidreq7               : out std_logic;                                         -- invalidreq7
            invalidreq8               : out std_logic;                                         -- invalidreq8
            invalidreq9               : out std_logic;                                         -- invalidreq9
            invalidreq10              : out std_logic;                                         -- invalidreq10
            invalidreq11              : out std_logic;                                         -- invalidreq11
            invalidreq12              : out std_logic;                                         -- invalidreq12
            invalidreq13              : out std_logic;                                         -- invalidreq13
            invalidreq14              : out std_logic;                                         -- invalidreq14
            invalidreq15              : out std_logic;                                         -- invalidreq15
            rxdata0                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata0
            rxdata1                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata1
            rxdata2                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata2
            rxdata3                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata3
            rxdata4                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata4
            rxdata5                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata5
            rxdata6                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata6
            rxdata7                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata7
            rxdata8                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata8
            rxdata9                   : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata9
            rxdata10                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata10
            rxdata11                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata11
            rxdata12                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata12
            rxdata13                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata13
            rxdata14                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata14
            rxdata15                  : in  std_logic_vector(31 downto 0)  := (others => 'X'); -- rxdata15
            rxdatak0                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak0
            rxdatak1                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak1
            rxdatak2                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak2
            rxdatak3                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak3
            rxdatak4                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak4
            rxdatak5                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak5
            rxdatak6                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak6
            rxdatak7                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak7
            rxdatak8                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak8
            rxdatak9                  : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak9
            rxdatak10                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak10
            rxdatak11                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak11
            rxdatak12                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak12
            rxdatak13                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak13
            rxdatak14                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak14
            rxdatak15                 : in  std_logic_vector(3 downto 0)   := (others => 'X'); -- rxdatak15
            phystatus0                : in  std_logic                      := 'X';             -- phystatus0
            phystatus1                : in  std_logic                      := 'X';             -- phystatus1
            phystatus2                : in  std_logic                      := 'X';             -- phystatus2
            phystatus3                : in  std_logic                      := 'X';             -- phystatus3
            phystatus4                : in  std_logic                      := 'X';             -- phystatus4
            phystatus5                : in  std_logic                      := 'X';             -- phystatus5
            phystatus6                : in  std_logic                      := 'X';             -- phystatus6
            phystatus7                : in  std_logic                      := 'X';             -- phystatus7
            phystatus8                : in  std_logic                      := 'X';             -- phystatus8
            phystatus9                : in  std_logic                      := 'X';             -- phystatus9
            phystatus10               : in  std_logic                      := 'X';             -- phystatus10
            phystatus11               : in  std_logic                      := 'X';             -- phystatus11
            phystatus12               : in  std_logic                      := 'X';             -- phystatus12
            phystatus13               : in  std_logic                      := 'X';             -- phystatus13
            phystatus14               : in  std_logic                      := 'X';             -- phystatus14
            phystatus15               : in  std_logic                      := 'X';             -- phystatus15
            rxvalid0                  : in  std_logic                      := 'X';             -- rxvalid0
            rxvalid1                  : in  std_logic                      := 'X';             -- rxvalid1
            rxvalid2                  : in  std_logic                      := 'X';             -- rxvalid2
            rxvalid3                  : in  std_logic                      := 'X';             -- rxvalid3
            rxvalid4                  : in  std_logic                      := 'X';             -- rxvalid4
            rxvalid5                  : in  std_logic                      := 'X';             -- rxvalid5
            rxvalid6                  : in  std_logic                      := 'X';             -- rxvalid6
            rxvalid7                  : in  std_logic                      := 'X';             -- rxvalid7
            rxvalid8                  : in  std_logic                      := 'X';             -- rxvalid8
            rxvalid9                  : in  std_logic                      := 'X';             -- rxvalid9
            rxvalid10                 : in  std_logic                      := 'X';             -- rxvalid10
            rxvalid11                 : in  std_logic                      := 'X';             -- rxvalid11
            rxvalid12                 : in  std_logic                      := 'X';             -- rxvalid12
            rxvalid13                 : in  std_logic                      := 'X';             -- rxvalid13
            rxvalid14                 : in  std_logic                      := 'X';             -- rxvalid14
            rxvalid15                 : in  std_logic                      := 'X';             -- rxvalid15
            rxstatus0                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus0
            rxstatus1                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus1
            rxstatus2                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus2
            rxstatus3                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus3
            rxstatus4                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus4
            rxstatus5                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus5
            rxstatus6                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus6
            rxstatus7                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus7
            rxstatus8                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus8
            rxstatus9                 : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus9
            rxstatus10                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus10
            rxstatus11                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus11
            rxstatus12                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus12
            rxstatus13                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus13
            rxstatus14                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus14
            rxstatus15                : in  std_logic_vector(2 downto 0)   := (others => 'X'); -- rxstatus15
            rxelecidle0               : in  std_logic                      := 'X';             -- rxelecidle0
            rxelecidle1               : in  std_logic                      := 'X';             -- rxelecidle1
            rxelecidle2               : in  std_logic                      := 'X';             -- rxelecidle2
            rxelecidle3               : in  std_logic                      := 'X';             -- rxelecidle3
            rxelecidle4               : in  std_logic                      := 'X';             -- rxelecidle4
            rxelecidle5               : in  std_logic                      := 'X';             -- rxelecidle5
            rxelecidle6               : in  std_logic                      := 'X';             -- rxelecidle6
            rxelecidle7               : in  std_logic                      := 'X';             -- rxelecidle7
            rxelecidle8               : in  std_logic                      := 'X';             -- rxelecidle8
            rxelecidle9               : in  std_logic                      := 'X';             -- rxelecidle9
            rxelecidle10              : in  std_logic                      := 'X';             -- rxelecidle10
            rxelecidle11              : in  std_logic                      := 'X';             -- rxelecidle11
            rxelecidle12              : in  std_logic                      := 'X';             -- rxelecidle12
            rxelecidle13              : in  std_logic                      := 'X';             -- rxelecidle13
            rxelecidle14              : in  std_logic                      := 'X';             -- rxelecidle14
            rxelecidle15              : in  std_logic                      := 'X';             -- rxelecidle15
            rxsynchd0                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd0
            rxsynchd1                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd1
            rxsynchd2                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd2
            rxsynchd3                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd3
            rxsynchd4                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd4
            rxsynchd5                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd5
            rxsynchd6                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd6
            rxsynchd7                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd7
            rxsynchd8                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd8
            rxsynchd9                 : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd9
            rxsynchd10                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd10
            rxsynchd11                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd11
            rxsynchd12                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd12
            rxsynchd13                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd13
            rxsynchd14                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd14
            rxsynchd15                : in  std_logic_vector(1 downto 0)   := (others => 'X'); -- rxsynchd15
            rxblkst0                  : in  std_logic                      := 'X';             -- rxblkst0
            rxblkst1                  : in  std_logic                      := 'X';             -- rxblkst1
            rxblkst2                  : in  std_logic                      := 'X';             -- rxblkst2
            rxblkst3                  : in  std_logic                      := 'X';             -- rxblkst3
            rxblkst4                  : in  std_logic                      := 'X';             -- rxblkst4
            rxblkst5                  : in  std_logic                      := 'X';             -- rxblkst5
            rxblkst6                  : in  std_logic                      := 'X';             -- rxblkst6
            rxblkst7                  : in  std_logic                      := 'X';             -- rxblkst7
            rxblkst8                  : in  std_logic                      := 'X';             -- rxblkst8
            rxblkst9                  : in  std_logic                      := 'X';             -- rxblkst9
            rxblkst10                 : in  std_logic                      := 'X';             -- rxblkst10
            rxblkst11                 : in  std_logic                      := 'X';             -- rxblkst11
            rxblkst12                 : in  std_logic                      := 'X';             -- rxblkst12
            rxblkst13                 : in  std_logic                      := 'X';             -- rxblkst13
            rxblkst14                 : in  std_logic                      := 'X';             -- rxblkst14
            rxblkst15                 : in  std_logic                      := 'X';             -- rxblkst15
            rxdataskip0               : in  std_logic                      := 'X';             -- rxdataskip0
            rxdataskip1               : in  std_logic                      := 'X';             -- rxdataskip1
            rxdataskip2               : in  std_logic                      := 'X';             -- rxdataskip2
            rxdataskip3               : in  std_logic                      := 'X';             -- rxdataskip3
            rxdataskip4               : in  std_logic                      := 'X';             -- rxdataskip4
            rxdataskip5               : in  std_logic                      := 'X';             -- rxdataskip5
            rxdataskip6               : in  std_logic                      := 'X';             -- rxdataskip6
            rxdataskip7               : in  std_logic                      := 'X';             -- rxdataskip7
            rxdataskip8               : in  std_logic                      := 'X';             -- rxdataskip8
            rxdataskip9               : in  std_logic                      := 'X';             -- rxdataskip9
            rxdataskip10              : in  std_logic                      := 'X';             -- rxdataskip10
            rxdataskip11              : in  std_logic                      := 'X';             -- rxdataskip11
            rxdataskip12              : in  std_logic                      := 'X';             -- rxdataskip12
            rxdataskip13              : in  std_logic                      := 'X';             -- rxdataskip13
            rxdataskip14              : in  std_logic                      := 'X';             -- rxdataskip14
            rxdataskip15              : in  std_logic                      := 'X';             -- rxdataskip15
            dirfeedback0              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback0
            dirfeedback1              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback1
            dirfeedback2              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback2
            dirfeedback3              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback3
            dirfeedback4              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback4
            dirfeedback5              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback5
            dirfeedback6              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback6
            dirfeedback7              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback7
            dirfeedback8              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback8
            dirfeedback9              : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback9
            dirfeedback10             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback10
            dirfeedback11             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback11
            dirfeedback12             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback12
            dirfeedback13             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback13
            dirfeedback14             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback14
            dirfeedback15             : in  std_logic_vector(5 downto 0)   := (others => 'X'); -- dirfeedback15
            sim_pipe_mask_tx_pll_lock : in  std_logic                      := 'X';             -- sim_pipe_mask_tx_pll_lock
            rx_in0                    : in  std_logic                      := 'X';             -- rx_in0
            rx_in1                    : in  std_logic                      := 'X';             -- rx_in1
            rx_in2                    : in  std_logic                      := 'X';             -- rx_in2
            rx_in3                    : in  std_logic                      := 'X';             -- rx_in3
            rx_in4                    : in  std_logic                      := 'X';             -- rx_in4
            rx_in5                    : in  std_logic                      := 'X';             -- rx_in5
            rx_in6                    : in  std_logic                      := 'X';             -- rx_in6
            rx_in7                    : in  std_logic                      := 'X';             -- rx_in7
            rx_in8                    : in  std_logic                      := 'X';             -- rx_in8
            rx_in9                    : in  std_logic                      := 'X';             -- rx_in9
            rx_in10                   : in  std_logic                      := 'X';             -- rx_in10
            rx_in11                   : in  std_logic                      := 'X';             -- rx_in11
            rx_in12                   : in  std_logic                      := 'X';             -- rx_in12
            rx_in13                   : in  std_logic                      := 'X';             -- rx_in13
            rx_in14                   : in  std_logic                      := 'X';             -- rx_in14
            rx_in15                   : in  std_logic                      := 'X';             -- rx_in15
            tx_out0                   : out std_logic;                                         -- tx_out0
            tx_out1                   : out std_logic;                                         -- tx_out1
            tx_out2                   : out std_logic;                                         -- tx_out2
            tx_out3                   : out std_logic;                                         -- tx_out3
            tx_out4                   : out std_logic;                                         -- tx_out4
            tx_out5                   : out std_logic;                                         -- tx_out5
            tx_out6                   : out std_logic;                                         -- tx_out6
            tx_out7                   : out std_logic;                                         -- tx_out7
            tx_out8                   : out std_logic;                                         -- tx_out8
            tx_out9                   : out std_logic;                                         -- tx_out9
            tx_out10                  : out std_logic;                                         -- tx_out10
            tx_out11                  : out std_logic;                                         -- tx_out11
            tx_out12                  : out std_logic;                                         -- tx_out12
            tx_out13                  : out std_logic;                                         -- tx_out13
            tx_out14                  : out std_logic;                                         -- tx_out14
            tx_out15                  : out std_logic;                                         -- tx_out15
            pm_linkst_in_l1           : out std_logic;                                         -- pm_linkst_in_l1
            pm_linkst_in_l0s          : out std_logic;                                         -- pm_linkst_in_l0s
            pm_state                  : out std_logic_vector(2 downto 0);                      -- pm_state
            pm_dstate                 : out std_logic_vector(2 downto 0);                      -- pm_dstate
            apps_pm_xmt_pme           : in  std_logic                      := 'X';             -- apps_pm_xmt_pme
            apps_ready_entr_l23       : in  std_logic                      := 'X';             -- apps_ready_entr_l23
            apps_pm_xmt_turnoff       : in  std_logic                      := 'X';             -- apps_pm_xmt_turnoff
            app_init_rst              : in  std_logic                      := 'X';             -- app_init_rst
            app_xfer_pending          : in  std_logic                      := 'X'             -- app_xfer_pending
            --flr_rcvd_vf               : out std_logic;                                         -- flr_rcvd_vf
            --flr_rcvd_pf_num           : out std_logic_vector(0 downto 0);                      -- flr_rcvd_pf_num
            --flr_rcvd_vf_num           : out std_logic_vector(0 downto 0);                      -- flr_rcvd_vf_num
            --flr_completed_vf          : in  std_logic                      := 'X';             -- flr_completed_vf
            --flr_completed_pf_num      : in  std_logic_vector(0 downto 0)   := (others => 'X'); -- flr_completed_pf_num
            --flr_completed_vf_num      : in  std_logic_vector(0 downto 0)   := (others => 'X')  -- flr_completed_vf_num
        );
    end component htile_pcie_1x16;

    constant PCIE_HIPS              : natural := tsel(ENDPOINT_MODE=0,PCIE_ENDPOINTS,PCIE_ENDPOINTS/2);
    constant CQ_FIFO_ITEMS          : natural := 512;
    constant VSEC_BASE_ADDRESS      : integer := 16#D00#;

    signal pcie_ceb_ack  : std_logic;
    signal pcie_ceb_din  : std_logic_vector(31 downto 0);
    signal pcie_ceb_addr : std_logic_vector(12-1 downto 0);
    signal pcie_ceb_req  : std_logic;
    signal pcie_ceb_dout : std_logic_vector(31 downto 0);
    signal pcie_ceb_wr   : std_logic_vector(3 downto 0);

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_reset_status        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_init_done_n         : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);

    signal pcie_avst_down_data      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_down_sop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_eop       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_empty     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_bar_range : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS*3-1 downto 0);
    signal pcie_avst_down_valid     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CQ_MFB_REGIONS-1 downto 0);
    signal pcie_avst_down_ready     : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '1');
    signal pcie_avst_up_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS*256-1 downto 0);
    signal pcie_avst_up_sop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_eop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_error       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0);
    signal pcie_avst_up_valid       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(CC_MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal pcie_avst_up_ready       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_link_up_comb        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_link_up_reg         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

begin

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_core_i : component htile_pcie_1x16
    port map (
        refclk                    => PCIE_SYSCLK_P(0),                    --         refclk.clk
        coreclkout_hip            => pcie_hip_clk(0),            -- coreclkout_hip.clk
        npor                      => PCIE_SYSRST_N(0),                      --           npor.npor
        pin_perst                 => PCIE_SYSRST_N(0),                 --               .pin_perst
        reset_status              => pcie_reset_status(0),              --        hip_rst.reset_status
        serdes_pll_locked         => open,         --               .serdes_pll_locked
        pld_core_ready            => '1',            --               .pld_core_ready
        pld_clk_inuse             => open,             --               .pld_clk_inuse
        testin_zero               => open,               --               .testin_zero
        clr_st                    => open,                    --         clr_st.reset
        ninit_done                => pcie_init_done_n(0),                --     ninit_done.ninit_done
        rx_st_ready               => pcie_avst_down_ready(0),               --          rx_st.ready
        rx_st_sop                 => pcie_avst_down_sop(0),                 --               .startofpacket
        rx_st_eop                 => pcie_avst_down_eop(0),                 --               .endofpacket
        rx_st_data                => pcie_avst_down_data(0)(512-1 downto 0),                --               .data
        rx_st_valid               => pcie_avst_down_valid(0)(2-1 downto 0),               --               .valid
        rx_st_empty               => pcie_avst_down_empty(0)(6-1 downto 0),               --               .empty
        tx_st_sop                 => pcie_avst_up_sop(0),                 --          tx_st.startofpacket
        tx_st_eop                 => pcie_avst_up_eop(0),                 --               .endofpacket
        tx_st_data                => pcie_avst_up_data(0)(512-1 downto 0),                --               .data
        tx_st_valid               => pcie_avst_up_valid(0),               --               .valid
        tx_st_err                 => pcie_avst_up_error(0),                 --               .error
        tx_st_ready               => pcie_avst_up_ready(0),               --               .ready
        rx_st_bar_range           => pcie_avst_down_bar_range(0),           --         rx_bar.rx_st_bar_range
        tx_cdts_type              => open,              --        tx_cred.tx_cdts_type
        tx_data_cdts_consumed     => open,     --               .tx_data_cdts_consumed
        tx_hdr_cdts_consumed      => open,      --               .tx_hdr_cdts_consumed
        tx_cdts_data_value        => open,        --               .tx_cdts_data_value
        tx_cpld_cdts              => open,              --               .tx_cpld_cdts
        tx_pd_cdts                => open,                --               .tx_pd_cdts
        tx_npd_cdts               => open,               --               .tx_npd_cdts
        tx_cplh_cdts              => open,              --               .tx_cplh_cdts
        tx_ph_cdts                => open,                --               .tx_ph_cdts
        tx_nph_cdts               => open,               --               .tx_nph_cdts
        app_msi_req               => '0',               --        int_msi.app_msi_req
        app_msi_ack               => open,               --               .app_msi_ack
        app_msi_tc                => (others => '0'),                --               .app_msi_tc
        app_msi_num               => (others => '0'),               --               .app_msi_num
        app_int_sts               => (others => '0'),               --               .app_int_sts
        app_msi_func_num          => (others => '0'),          --               .app_msi_func_num
        int_status                => open,                --     hip_status.int_status
        int_status_common         => open,         --               .int_status_common
        derr_cor_ext_rpl          => open,          --               .derr_cor_ext_rpl
        derr_rpl                  => open,                  --               .derr_rpl
        derr_cor_ext_rcv          => open,          --               .derr_cor_ext_rcv
        derr_uncor_ext_rcv        => open,        --               .derr_uncor_ext_rcv
        rx_par_err                => open,                --               .rx_par_err
        tx_par_err                => open,                --               .tx_par_err
        ltssmstate                => open,                --               .ltssmstate
        link_up                   => pcie_link_up_comb(0),                   --               .link_up
        lane_act                  => open,                  --               .lane_act
        --flr_pf_done               => '0',               --       flr_ctrl.flr_pf_done
        --flr_pf_active             => open,             --               .flr_pf_active
        tl_cfg_func               => open,               --      config_tl.tl_cfg_func
        tl_cfg_add                => open,                --               .tl_cfg_add
        tl_cfg_ctl                => open,                --               .tl_cfg_ctl
        app_err_valid             => '0',             --               .app_err_valid
        app_err_hdr               => (others => '0'),               --               .app_err_hdr
        app_err_info              => (others => '0'),              --               .app_err_info
        app_err_func_num          => (others => '0'),          --               .app_err_func_num
        test_in                   => (others => '0'),                   --       hip_ctrl.test_in
        simu_mode_pipe            => '0',            --               .simu_mode_pipe
        currentspeed              => open,              --   currentspeed.currentspeed
        ceb_ack                   => pcie_ceb_ack,                   --            ceb.ceb_ack
        ceb_din                   => pcie_ceb_din,                   --               .ceb_din
        ceb_addr                  => pcie_ceb_addr,                  --               .ceb_addr
        ceb_req                   => pcie_ceb_req,                   --               .ceb_req
        ceb_dout                  => pcie_ceb_dout,                  --               .ceb_dout
        ceb_wr                    => pcie_ceb_wr,                    --               .ceb_wr
        ceb_cdm_convert_data      => (others => '0'),      --               .ceb_cdm_convert_data
        ceb_func_num              => open,              --               .ceb_func_num
        sim_pipe_pclk_in          => '0',          --       hip_pipe.sim_pipe_pclk_in
        sim_pipe_rate             => open,             --               .sim_pipe_rate
        sim_ltssmstate            => open,            --               .sim_ltssmstate
        txdata0                   => open,                   --               .txdata0
        txdata1                   => open,                   --               .txdata1
        txdata2                   => open,                   --               .txdata2
        txdata3                   => open,                   --               .txdata3
        txdata4                   => open,                   --               .txdata4
        txdata5                   => open,                   --               .txdata5
        txdata6                   => open,                   --               .txdata6
        txdata7                   => open,                   --               .txdata7
        txdata8                   => open,                   --               .txdata8
        txdata9                   => open,                   --               .txdata9
        txdata10                  => open,                  --               .txdata10
        txdata11                  => open,                  --               .txdata11
        txdata12                  => open,                  --               .txdata12
        txdata13                  => open,                  --               .txdata13
        txdata14                  => open,                  --               .txdata14
        txdata15                  => open,                  --               .txdata15
        txdatak0                  => open,                  --               .txdatak0
        txdatak1                  => open,                  --               .txdatak1
        txdatak2                  => open,                  --               .txdatak2
        txdatak3                  => open,                  --               .txdatak3
        txdatak4                  => open,                  --               .txdatak4
        txdatak5                  => open,                  --               .txdatak5
        txdatak6                  => open,                  --               .txdatak6
        txdatak7                  => open,                  --               .txdatak7
        txdatak8                  => open,                  --               .txdatak8
        txdatak9                  => open,                  --               .txdatak9
        txdatak10                 => open,                 --               .txdatak10
        txdatak11                 => open,                 --               .txdatak11
        txdatak12                 => open,                 --               .txdatak12
        txdatak13                 => open,                 --               .txdatak13
        txdatak14                 => open,                 --               .txdatak14
        txdatak15                 => open,                 --               .txdatak15
        txcompl0                  => open,                  --               .txcompl0
        txcompl1                  => open,                  --               .txcompl1
        txcompl2                  => open,                  --               .txcompl2
        txcompl3                  => open,                  --               .txcompl3
        txcompl4                  => open,                  --               .txcompl4
        txcompl5                  => open,                  --               .txcompl5
        txcompl6                  => open,                  --               .txcompl6
        txcompl7                  => open,                  --               .txcompl7
        txcompl8                  => open,                  --               .txcompl8
        txcompl9                  => open,                  --               .txcompl9
        txcompl10                 => open,                 --               .txcompl10
        txcompl11                 => open,                 --               .txcompl11
        txcompl12                 => open,                 --               .txcompl12
        txcompl13                 => open,                 --               .txcompl13
        txcompl14                 => open,                 --               .txcompl14
        txcompl15                 => open,                 --               .txcompl15
        txelecidle0               => open,               --               .txelecidle0
        txelecidle1               => open,               --               .txelecidle1
        txelecidle2               => open,               --               .txelecidle2
        txelecidle3               => open,               --               .txelecidle3
        txelecidle4               => open,               --               .txelecidle4
        txelecidle5               => open,               --               .txelecidle5
        txelecidle6               => open,               --               .txelecidle6
        txelecidle7               => open,               --               .txelecidle7
        txelecidle8               => open,               --               .txelecidle8
        txelecidle9               => open,               --               .txelecidle9
        txelecidle10              => open,              --               .txelecidle10
        txelecidle11              => open,              --               .txelecidle11
        txelecidle12              => open,              --               .txelecidle12
        txelecidle13              => open,              --               .txelecidle13
        txelecidle14              => open,              --               .txelecidle14
        txelecidle15              => open,              --               .txelecidle15
        txdetectrx0               => open,               --               .txdetectrx0
        txdetectrx1               => open,               --               .txdetectrx1
        txdetectrx2               => open,               --               .txdetectrx2
        txdetectrx3               => open,               --               .txdetectrx3
        txdetectrx4               => open,               --               .txdetectrx4
        txdetectrx5               => open,               --               .txdetectrx5
        txdetectrx6               => open,               --               .txdetectrx6
        txdetectrx7               => open,               --               .txdetectrx7
        txdetectrx8               => open,               --               .txdetectrx8
        txdetectrx9               => open,               --               .txdetectrx9
        txdetectrx10              => open,              --               .txdetectrx10
        txdetectrx11              => open,              --               .txdetectrx11
        txdetectrx12              => open,              --               .txdetectrx12
        txdetectrx13              => open,              --               .txdetectrx13
        txdetectrx14              => open,              --               .txdetectrx14
        txdetectrx15              => open,              --               .txdetectrx15
        powerdown0                => open,                --               .powerdown0
        powerdown1                => open,                --               .powerdown1
        powerdown2                => open,                --               .powerdown2
        powerdown3                => open,                --               .powerdown3
        powerdown4                => open,                --               .powerdown4
        powerdown5                => open,                --               .powerdown5
        powerdown6                => open,                --               .powerdown6
        powerdown7                => open,                --               .powerdown7
        powerdown8                => open,                --               .powerdown8
        powerdown9                => open,                --               .powerdown9
        powerdown10               => open,               --               .powerdown10
        powerdown11               => open,               --               .powerdown11
        powerdown12               => open,               --               .powerdown12
        powerdown13               => open,               --               .powerdown13
        powerdown14               => open,               --               .powerdown14
        powerdown15               => open,               --               .powerdown15
        txmargin0                 => open,                 --               .txmargin0
        txmargin1                 => open,                 --               .txmargin1
        txmargin2                 => open,                 --               .txmargin2
        txmargin3                 => open,                 --               .txmargin3
        txmargin4                 => open,                 --               .txmargin4
        txmargin5                 => open,                 --               .txmargin5
        txmargin6                 => open,                 --               .txmargin6
        txmargin7                 => open,                 --               .txmargin7
        txmargin8                 => open,                 --               .txmargin8
        txmargin9                 => open,                 --               .txmargin9
        txmargin10                => open,                --               .txmargin10
        txmargin11                => open,                --               .txmargin11
        txmargin12                => open,                --               .txmargin12
        txmargin13                => open,                --               .txmargin13
        txmargin14                => open,                --               .txmargin14
        txmargin15                => open,                --               .txmargin15
        txdeemph0                 => open,                 --               .txdeemph0
        txdeemph1                 => open,                 --               .txdeemph1
        txdeemph2                 => open,                 --               .txdeemph2
        txdeemph3                 => open,                 --               .txdeemph3
        txdeemph4                 => open,                 --               .txdeemph4
        txdeemph5                 => open,                 --               .txdeemph5
        txdeemph6                 => open,                 --               .txdeemph6
        txdeemph7                 => open,                 --               .txdeemph7
        txdeemph8                 => open,                 --               .txdeemph8
        txdeemph9                 => open,                 --               .txdeemph9
        txdeemph10                => open,                --               .txdeemph10
        txdeemph11                => open,                --               .txdeemph11
        txdeemph12                => open,                --               .txdeemph12
        txdeemph13                => open,                --               .txdeemph13
        txdeemph14                => open,                --               .txdeemph14
        txdeemph15                => open,                --               .txdeemph15
        txswing0                  => open,                  --               .txswing0
        txswing1                  => open,                  --               .txswing1
        txswing2                  => open,                  --               .txswing2
        txswing3                  => open,                  --               .txswing3
        txswing4                  => open,                  --               .txswing4
        txswing5                  => open,                  --               .txswing5
        txswing6                  => open,                  --               .txswing6
        txswing7                  => open,                  --               .txswing7
        txswing8                  => open,                  --               .txswing8
        txswing9                  => open,                  --               .txswing9
        txswing10                 => open,                 --               .txswing10
        txswing11                 => open,                 --               .txswing11
        txswing12                 => open,                 --               .txswing12
        txswing13                 => open,                 --               .txswing13
        txswing14                 => open,                 --               .txswing14
        txswing15                 => open,                 --               .txswing15
        txsynchd0                 => open,                 --               .txsynchd0
        txsynchd1                 => open,                 --               .txsynchd1
        txsynchd2                 => open,                 --               .txsynchd2
        txsynchd3                 => open,                 --               .txsynchd3
        txsynchd4                 => open,                 --               .txsynchd4
        txsynchd5                 => open,                 --               .txsynchd5
        txsynchd6                 => open,                 --               .txsynchd6
        txsynchd7                 => open,                 --               .txsynchd7
        txsynchd8                 => open,                 --               .txsynchd8
        txsynchd9                 => open,                 --               .txsynchd9
        txsynchd10                => open,                --               .txsynchd10
        txsynchd11                => open,                --               .txsynchd11
        txsynchd12                => open,                --               .txsynchd12
        txsynchd13                => open,                --               .txsynchd13
        txsynchd14                => open,                --               .txsynchd14
        txsynchd15                => open,                --               .txsynchd15
        txblkst0                  => open,                  --               .txblkst0
        txblkst1                  => open,                  --               .txblkst1
        txblkst2                  => open,                  --               .txblkst2
        txblkst3                  => open,                  --               .txblkst3
        txblkst4                  => open,                  --               .txblkst4
        txblkst5                  => open,                  --               .txblkst5
        txblkst6                  => open,                  --               .txblkst6
        txblkst7                  => open,                  --               .txblkst7
        txblkst8                  => open,                  --               .txblkst8
        txblkst9                  => open,                  --               .txblkst9
        txblkst10                 => open,                 --               .txblkst10
        txblkst11                 => open,                 --               .txblkst11
        txblkst12                 => open,                 --               .txblkst12
        txblkst13                 => open,                 --               .txblkst13
        txblkst14                 => open,                 --               .txblkst14
        txblkst15                 => open,                 --               .txblkst15
        txdataskip0               => open,               --               .txdataskip0
        txdataskip1               => open,               --               .txdataskip1
        txdataskip2               => open,               --               .txdataskip2
        txdataskip3               => open,               --               .txdataskip3
        txdataskip4               => open,               --               .txdataskip4
        txdataskip5               => open,               --               .txdataskip5
        txdataskip6               => open,               --               .txdataskip6
        txdataskip7               => open,               --               .txdataskip7
        txdataskip8               => open,               --               .txdataskip8
        txdataskip9               => open,               --               .txdataskip9
        txdataskip10              => open,              --               .txdataskip10
        txdataskip11              => open,              --               .txdataskip11
        txdataskip12              => open,              --               .txdataskip12
        txdataskip13              => open,              --               .txdataskip13
        txdataskip14              => open,              --               .txdataskip14
        txdataskip15              => open,              --               .txdataskip15
        rate0                     => open,                     --               .rate0
        rate1                     => open,                     --               .rate1
        rate2                     => open,                     --               .rate2
        rate3                     => open,                     --               .rate3
        rate4                     => open,                     --               .rate4
        rate5                     => open,                     --               .rate5
        rate6                     => open,                     --               .rate6
        rate7                     => open,                     --               .rate7
        rate8                     => open,                     --               .rate8
        rate9                     => open,                     --               .rate9
        rate10                    => open,                    --               .rate10
        rate11                    => open,                    --               .rate11
        rate12                    => open,                    --               .rate12
        rate13                    => open,                    --               .rate13
        rate14                    => open,                    --               .rate14
        rate15                    => open,                    --               .rate15
        rxpolarity0               => open,               --               .rxpolarity0
        rxpolarity1               => open,               --               .rxpolarity1
        rxpolarity2               => open,               --               .rxpolarity2
        rxpolarity3               => open,               --               .rxpolarity3
        rxpolarity4               => open,               --               .rxpolarity4
        rxpolarity5               => open,               --               .rxpolarity5
        rxpolarity6               => open,               --               .rxpolarity6
        rxpolarity7               => open,               --               .rxpolarity7
        rxpolarity8               => open,               --               .rxpolarity8
        rxpolarity9               => open,               --               .rxpolarity9
        rxpolarity10              => open,              --               .rxpolarity10
        rxpolarity11              => open,              --               .rxpolarity11
        rxpolarity12              => open,              --               .rxpolarity12
        rxpolarity13              => open,              --               .rxpolarity13
        rxpolarity14              => open,              --               .rxpolarity14
        rxpolarity15              => open,              --               .rxpolarity15
        currentrxpreset0          => open,          --               .currentrxpreset0
        currentrxpreset1          => open,          --               .currentrxpreset1
        currentrxpreset2          => open,          --               .currentrxpreset2
        currentrxpreset3          => open,          --               .currentrxpreset3
        currentrxpreset4          => open,          --               .currentrxpreset4
        currentrxpreset5          => open,          --               .currentrxpreset5
        currentrxpreset6          => open,          --               .currentrxpreset6
        currentrxpreset7          => open,          --               .currentrxpreset7
        currentrxpreset8          => open,          --               .currentrxpreset8
        currentrxpreset9          => open,          --               .currentrxpreset9
        currentrxpreset10         => open,         --               .currentrxpreset10
        currentrxpreset11         => open,         --               .currentrxpreset11
        currentrxpreset12         => open,         --               .currentrxpreset12
        currentrxpreset13         => open,         --               .currentrxpreset13
        currentrxpreset14         => open,         --               .currentrxpreset14
        currentrxpreset15         => open,         --               .currentrxpreset15
        currentcoeff0             => open,             --               .currentcoeff0
        currentcoeff1             => open,             --               .currentcoeff1
        currentcoeff2             => open,             --               .currentcoeff2
        currentcoeff3             => open,             --               .currentcoeff3
        currentcoeff4             => open,             --               .currentcoeff4
        currentcoeff5             => open,             --               .currentcoeff5
        currentcoeff6             => open,             --               .currentcoeff6
        currentcoeff7             => open,             --               .currentcoeff7
        currentcoeff8             => open,             --               .currentcoeff8
        currentcoeff9             => open,             --               .currentcoeff9
        currentcoeff10            => open,            --               .currentcoeff10
        currentcoeff11            => open,            --               .currentcoeff11
        currentcoeff12            => open,            --               .currentcoeff12
        currentcoeff13            => open,            --               .currentcoeff13
        currentcoeff14            => open,            --               .currentcoeff14
        currentcoeff15            => open,            --               .currentcoeff15
        rxeqeval0                 => open,                 --               .rxeqeval0
        rxeqeval1                 => open,                 --               .rxeqeval1
        rxeqeval2                 => open,                 --               .rxeqeval2
        rxeqeval3                 => open,                 --               .rxeqeval3
        rxeqeval4                 => open,                 --               .rxeqeval4
        rxeqeval5                 => open,                 --               .rxeqeval5
        rxeqeval6                 => open,                 --               .rxeqeval6
        rxeqeval7                 => open,                 --               .rxeqeval7
        rxeqeval8                 => open,                 --               .rxeqeval8
        rxeqeval9                 => open,                 --               .rxeqeval9
        rxeqeval10                => open,                --               .rxeqeval10
        rxeqeval11                => open,                --               .rxeqeval11
        rxeqeval12                => open,                --               .rxeqeval12
        rxeqeval13                => open,                --               .rxeqeval13
        rxeqeval14                => open,                --               .rxeqeval14
        rxeqeval15                => open,                --               .rxeqeval15
        rxeqinprogress0           => open,           --               .rxeqinprogress0
        rxeqinprogress1           => open,           --               .rxeqinprogress1
        rxeqinprogress2           => open,           --               .rxeqinprogress2
        rxeqinprogress3           => open,           --               .rxeqinprogress3
        rxeqinprogress4           => open,           --               .rxeqinprogress4
        rxeqinprogress5           => open,           --               .rxeqinprogress5
        rxeqinprogress6           => open,           --               .rxeqinprogress6
        rxeqinprogress7           => open,           --               .rxeqinprogress7
        rxeqinprogress8           => open,           --               .rxeqinprogress8
        rxeqinprogress9           => open,           --               .rxeqinprogress9
        rxeqinprogress10          => open,          --               .rxeqinprogress10
        rxeqinprogress11          => open,          --               .rxeqinprogress11
        rxeqinprogress12          => open,          --               .rxeqinprogress12
        rxeqinprogress13          => open,          --               .rxeqinprogress13
        rxeqinprogress14          => open,          --               .rxeqinprogress14
        rxeqinprogress15          => open,          --               .rxeqinprogress15
        invalidreq0               => open,               --               .invalidreq0
        invalidreq1               => open,               --               .invalidreq1
        invalidreq2               => open,               --               .invalidreq2
        invalidreq3               => open,               --               .invalidreq3
        invalidreq4               => open,               --               .invalidreq4
        invalidreq5               => open,               --               .invalidreq5
        invalidreq6               => open,               --               .invalidreq6
        invalidreq7               => open,               --               .invalidreq7
        invalidreq8               => open,               --               .invalidreq8
        invalidreq9               => open,               --               .invalidreq9
        invalidreq10              => open,              --               .invalidreq10
        invalidreq11              => open,              --               .invalidreq11
        invalidreq12              => open,              --               .invalidreq12
        invalidreq13              => open,              --               .invalidreq13
        invalidreq14              => open,              --               .invalidreq14
        invalidreq15              => open,              --               .invalidreq15
        rxdata0                   => (others => '0'),                   --               .rxdata0
        rxdata1                   => (others => '0'),                   --               .rxdata1
        rxdata2                   => (others => '0'),                   --               .rxdata2
        rxdata3                   => (others => '0'),                   --               .rxdata3
        rxdata4                   => (others => '0'),                   --               .rxdata4
        rxdata5                   => (others => '0'),                   --               .rxdata5
        rxdata6                   => (others => '0'),                   --               .rxdata6
        rxdata7                   => (others => '0'),                   --               .rxdata7
        rxdata8                   => (others => '0'),                   --               .rxdata8
        rxdata9                   => (others => '0'),                   --               .rxdata9
        rxdata10                  => (others => '0'),                  --               .rxdata10
        rxdata11                  => (others => '0'),                  --               .rxdata11
        rxdata12                  => (others => '0'),                  --               .rxdata12
        rxdata13                  => (others => '0'),                  --               .rxdata13
        rxdata14                  => (others => '0'),                  --               .rxdata14
        rxdata15                  => (others => '0'),                  --               .rxdata15
        rxdatak0                  => (others => '0'),                  --               .rxdatak0
        rxdatak1                  => (others => '0'),                  --               .rxdatak1
        rxdatak2                  => (others => '0'),                  --               .rxdatak2
        rxdatak3                  => (others => '0'),                  --               .rxdatak3
        rxdatak4                  => (others => '0'),                  --               .rxdatak4
        rxdatak5                  => (others => '0'),                  --               .rxdatak5
        rxdatak6                  => (others => '0'),                  --               .rxdatak6
        rxdatak7                  => (others => '0'),                  --               .rxdatak7
        rxdatak8                  => (others => '0'),                  --               .rxdatak8
        rxdatak9                  => (others => '0'),                  --               .rxdatak9
        rxdatak10                 => (others => '0'),                 --               .rxdatak10
        rxdatak11                 => (others => '0'),                 --               .rxdatak11
        rxdatak12                 => (others => '0'),                 --               .rxdatak12
        rxdatak13                 => (others => '0'),                 --               .rxdatak13
        rxdatak14                 => (others => '0'),                 --               .rxdatak14
        rxdatak15                 => (others => '0'),                 --               .rxdatak15
        phystatus0                => '0',                --               .phystatus0
        phystatus1                => '0',                --               .phystatus1
        phystatus2                => '0',                --               .phystatus2
        phystatus3                => '0',                --               .phystatus3
        phystatus4                => '0',                --               .phystatus4
        phystatus5                => '0',                --               .phystatus5
        phystatus6                => '0',                --               .phystatus6
        phystatus7                => '0',                --               .phystatus7
        phystatus8                => '0',                --               .phystatus8
        phystatus9                => '0',                --               .phystatus9
        phystatus10               => '0',               --               .phystatus10
        phystatus11               => '0',               --               .phystatus11
        phystatus12               => '0',               --               .phystatus12
        phystatus13               => '0',               --               .phystatus13
        phystatus14               => '0',               --               .phystatus14
        phystatus15               => '0',               --               .phystatus15
        rxvalid0                  => '0',                  --               .rxvalid0
        rxvalid1                  => '0',                  --               .rxvalid1
        rxvalid2                  => '0',                  --               .rxvalid2
        rxvalid3                  => '0',                  --               .rxvalid3
        rxvalid4                  => '0',                  --               .rxvalid4
        rxvalid5                  => '0',                  --               .rxvalid5
        rxvalid6                  => '0',                  --               .rxvalid6
        rxvalid7                  => '0',                  --               .rxvalid7
        rxvalid8                  => '0',                  --               .rxvalid8
        rxvalid9                  => '0',                  --               .rxvalid9
        rxvalid10                 => '0',                 --               .rxvalid10
        rxvalid11                 => '0',                 --               .rxvalid11
        rxvalid12                 => '0',                 --               .rxvalid12
        rxvalid13                 => '0',                 --               .rxvalid13
        rxvalid14                 => '0',                 --               .rxvalid14
        rxvalid15                 => '0',                 --               .rxvalid15
        rxstatus0                 => (others => '0'),                 --               .rxstatus0
        rxstatus1                 => (others => '0'),                 --               .rxstatus1
        rxstatus2                 => (others => '0'),                 --               .rxstatus2
        rxstatus3                 => (others => '0'),                 --               .rxstatus3
        rxstatus4                 => (others => '0'),                 --               .rxstatus4
        rxstatus5                 => (others => '0'),                 --               .rxstatus5
        rxstatus6                 => (others => '0'),                 --               .rxstatus6
        rxstatus7                 => (others => '0'),                 --               .rxstatus7
        rxstatus8                 => (others => '0'),                 --               .rxstatus8
        rxstatus9                 => (others => '0'),                 --               .rxstatus9
        rxstatus10                => (others => '0'),                --               .rxstatus10
        rxstatus11                => (others => '0'),                --               .rxstatus11
        rxstatus12                => (others => '0'),                --               .rxstatus12
        rxstatus13                => (others => '0'),                --               .rxstatus13
        rxstatus14                => (others => '0'),                --               .rxstatus14
        rxstatus15                => (others => '0'),                --               .rxstatus15
        rxelecidle0               => '0',               --               .rxelecidle0
        rxelecidle1               => '0',               --               .rxelecidle1
        rxelecidle2               => '0',               --               .rxelecidle2
        rxelecidle3               => '0',               --               .rxelecidle3
        rxelecidle4               => '0',               --               .rxelecidle4
        rxelecidle5               => '0',               --               .rxelecidle5
        rxelecidle6               => '0',               --               .rxelecidle6
        rxelecidle7               => '0',               --               .rxelecidle7
        rxelecidle8               => '0',               --               .rxelecidle8
        rxelecidle9               => '0',               --               .rxelecidle9
        rxelecidle10              => '0',              --               .rxelecidle10
        rxelecidle11              => '0',              --               .rxelecidle11
        rxelecidle12              => '0',              --               .rxelecidle12
        rxelecidle13              => '0',              --               .rxelecidle13
        rxelecidle14              => '0',              --               .rxelecidle14
        rxelecidle15              => '0',              --               .rxelecidle15
        rxsynchd0                 => (others => '0'),                 --               .rxsynchd0
        rxsynchd1                 => (others => '0'),                 --               .rxsynchd1
        rxsynchd2                 => (others => '0'),                 --               .rxsynchd2
        rxsynchd3                 => (others => '0'),                 --               .rxsynchd3
        rxsynchd4                 => (others => '0'),                 --               .rxsynchd4
        rxsynchd5                 => (others => '0'),                 --               .rxsynchd5
        rxsynchd6                 => (others => '0'),                 --               .rxsynchd6
        rxsynchd7                 => (others => '0'),                 --               .rxsynchd7
        rxsynchd8                 => (others => '0'),                 --               .rxsynchd8
        rxsynchd9                 => (others => '0'),                 --               .rxsynchd9
        rxsynchd10                => (others => '0'),                --               .rxsynchd10
        rxsynchd11                => (others => '0'),                --               .rxsynchd11
        rxsynchd12                => (others => '0'),                --               .rxsynchd12
        rxsynchd13                => (others => '0'),                --               .rxsynchd13
        rxsynchd14                => (others => '0'),                --               .rxsynchd14
        rxsynchd15                => (others => '0'),                --               .rxsynchd15
        rxblkst0                  => '0',                  --               .rxblkst0
        rxblkst1                  => '0',                  --               .rxblkst1
        rxblkst2                  => '0',                  --               .rxblkst2
        rxblkst3                  => '0',                  --               .rxblkst3
        rxblkst4                  => '0',                  --               .rxblkst4
        rxblkst5                  => '0',                  --               .rxblkst5
        rxblkst6                  => '0',                  --               .rxblkst6
        rxblkst7                  => '0',                  --               .rxblkst7
        rxblkst8                  => '0',                  --               .rxblkst8
        rxblkst9                  => '0',                  --               .rxblkst9
        rxblkst10                 => '0',                 --               .rxblkst10
        rxblkst11                 => '0',                 --               .rxblkst11
        rxblkst12                 => '0',                 --               .rxblkst12
        rxblkst13                 => '0',                 --               .rxblkst13
        rxblkst14                 => '0',                 --               .rxblkst14
        rxblkst15                 => '0',                 --               .rxblkst15
        rxdataskip0               => '0',               --               .rxdataskip0
        rxdataskip1               => '0',               --               .rxdataskip1
        rxdataskip2               => '0',               --               .rxdataskip2
        rxdataskip3               => '0',               --               .rxdataskip3
        rxdataskip4               => '0',               --               .rxdataskip4
        rxdataskip5               => '0',               --               .rxdataskip5
        rxdataskip6               => '0',               --               .rxdataskip6
        rxdataskip7               => '0',               --               .rxdataskip7
        rxdataskip8               => '0',               --               .rxdataskip8
        rxdataskip9               => '0',               --               .rxdataskip9
        rxdataskip10              => '0',              --               .rxdataskip10
        rxdataskip11              => '0',              --               .rxdataskip11
        rxdataskip12              => '0',              --               .rxdataskip12
        rxdataskip13              => '0',              --               .rxdataskip13
        rxdataskip14              => '0',              --               .rxdataskip14
        rxdataskip15              => '0',              --               .rxdataskip15
        dirfeedback0              => (others => '0'),              --               .dirfeedback0
        dirfeedback1              => (others => '0'),              --               .dirfeedback1
        dirfeedback2              => (others => '0'),              --               .dirfeedback2
        dirfeedback3              => (others => '0'),              --               .dirfeedback3
        dirfeedback4              => (others => '0'),              --               .dirfeedback4
        dirfeedback5              => (others => '0'),              --               .dirfeedback5
        dirfeedback6              => (others => '0'),              --               .dirfeedback6
        dirfeedback7              => (others => '0'),              --               .dirfeedback7
        dirfeedback8              => (others => '0'),              --               .dirfeedback8
        dirfeedback9              => (others => '0'),              --               .dirfeedback9
        dirfeedback10             => (others => '0'),             --               .dirfeedback10
        dirfeedback11             => (others => '0'),             --               .dirfeedback11
        dirfeedback12             => (others => '0'),             --               .dirfeedback12
        dirfeedback13             => (others => '0'),             --               .dirfeedback13
        dirfeedback14             => (others => '0'),             --               .dirfeedback14
        dirfeedback15             => (others => '0'),             --               .dirfeedback15
        sim_pipe_mask_tx_pll_lock => '0', --               .sim_pipe_mask_tx_pll_lock
        rx_in0                    => PCIE_RX_P(0),                    --     hip_serial.rx_in0
        rx_in1                    => PCIE_RX_P(1),                    --               .rx_in1
        rx_in2                    => PCIE_RX_P(2),                    --               .rx_in2
        rx_in3                    => PCIE_RX_P(3),                    --               .rx_in3
        rx_in4                    => PCIE_RX_P(4),                    --               .rx_in4
        rx_in5                    => PCIE_RX_P(5),                    --               .rx_in5
        rx_in6                    => PCIE_RX_P(6),                    --               .rx_in6
        rx_in7                    => PCIE_RX_P(7),                    --               .rx_in7
        rx_in8                    => PCIE_RX_P(8),                    --               .rx_in8
        rx_in9                    => PCIE_RX_P(9),                    --               .rx_in9
        rx_in10                   => PCIE_RX_P(10),                   --               .rx_in10
        rx_in11                   => PCIE_RX_P(11),                   --               .rx_in11
        rx_in12                   => PCIE_RX_P(12),                   --               .rx_in12
        rx_in13                   => PCIE_RX_P(13),                   --               .rx_in13
        rx_in14                   => PCIE_RX_P(14),                   --               .rx_in14
        rx_in15                   => PCIE_RX_P(15),                   --               .rx_in15
        tx_out0                   => PCIE_TX_P(0),                   --               .tx_out0
        tx_out1                   => PCIE_TX_P(1),                   --               .tx_out1
        tx_out2                   => PCIE_TX_P(2),                   --               .tx_out2
        tx_out3                   => PCIE_TX_P(3),                   --               .tx_out3
        tx_out4                   => PCIE_TX_P(4),                   --               .tx_out4
        tx_out5                   => PCIE_TX_P(5),                   --               .tx_out5
        tx_out6                   => PCIE_TX_P(6),                   --               .tx_out6
        tx_out7                   => PCIE_TX_P(7),                   --               .tx_out7
        tx_out8                   => PCIE_TX_P(8),                   --               .tx_out8
        tx_out9                   => PCIE_TX_P(9),                   --               .tx_out9
        tx_out10                  => PCIE_TX_P(10),                  --               .tx_out10
        tx_out11                  => PCIE_TX_P(11),                  --               .tx_out11
        tx_out12                  => PCIE_TX_P(12),                  --               .tx_out12
        tx_out13                  => PCIE_TX_P(13),                  --               .tx_out13
        tx_out14                  => PCIE_TX_P(14),                  --               .tx_out14
        tx_out15                  => PCIE_TX_P(15),                  --               .tx_out15
        pm_linkst_in_l1           => open,           --     power_mgnt.pm_linkst_in_l1
        pm_linkst_in_l0s          => open,          --               .pm_linkst_in_l0s
        pm_state                  => open,                  --               .pm_state
        pm_dstate                 => open,                 --               .pm_dstate
        apps_pm_xmt_pme           => '0',           --               .apps_pm_xmt_pme
        apps_ready_entr_l23       => '0',       --               .apps_ready_entr_l23
        apps_pm_xmt_turnoff       => '0',       --               .apps_pm_xmt_turnoff
        app_init_rst              => '0',              --               .app_init_rst
        app_xfer_pending          => '0'          --               .app_xfer_pending
        --flr_rcvd_vf               => open,               --    flr_ctrl_vf.flr_rcvd_vf
        --flr_rcvd_pf_num           => open,           --               .flr_rcvd_pf_num
        --flr_rcvd_vf_num           => open,           --               .flr_rcvd_vf_num
        --flr_completed_vf          => '0',          --               .flr_completed_vf
        --flr_completed_pf_num      => (others => '0'),      --               .flr_completed_pf_num
        --flr_completed_vf_num      => (others => '0')       --               .flr_completed_vf_num
    );

    PCIE_TX_N <= not PCIE_TX_P;

    pcie_clk(0)         <= pcie_hip_clk(0);
    pcie_init_done_n(0) <= INIT_DONE_N;

    -- =========================================================================
    --  UP/DOWN AVALON-ST INTERFACE
    -- =========================================================================

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
        ENDPOINT_TYPE      => "H_TILE",
        DEVICE             => DEVICE,
        CQ_FIFO_ITEMS      => CQ_FIFO_ITEMS,
        AXI_CQUSER_WIDTH   => 183,
        AXI_CCUSER_WIDTH   => 81,
        AXI_RQUSER_WIDTH   => 137,
        AXI_RCUSER_WIDTH   => 161,
        AXI_STRADDLING     => false
    )
    port map (
        PCIE_CLK            => pcie_clk(0),
        PCIE_RESET          => pcie_rst(0)(0),

        AVST_DOWN_DATA      => pcie_avst_down_data(0),
        AVST_DOWN_HDR       => (others => '0'), -- P-TILE only
        AVST_DOWN_PREFIX    => (others => '0'), -- P-TILE only
        AVST_DOWN_SOP       => pcie_avst_down_sop(0),
        AVST_DOWN_EOP       => pcie_avst_down_eop(0),
        AVST_DOWN_EMPTY     => pcie_avst_down_empty(0),
        AVST_DOWN_BAR_RANGE => pcie_avst_down_bar_range(0),
        AVST_DOWN_VALID     => pcie_avst_down_valid(0),
        AVST_DOWN_READY     => pcie_avst_down_ready(0),

        AVST_UP_DATA        => pcie_avst_up_data(0),
        AVST_UP_HDR         => open,
        AVST_UP_PREFIX      => open,
        AVST_UP_SOP         => pcie_avst_up_sop(0),
        AVST_UP_EOP         => pcie_avst_up_eop(0),
        AVST_UP_ERROR       => pcie_avst_up_error(0),
        AVST_UP_VALID       => pcie_avst_up_valid(0),
        AVST_UP_READY       => pcie_avst_up_ready(0),

        CRDT_DOWN_INIT_DONE => '0',
        CRDT_DOWN_UPDATE    => open,
        CRDT_DOWN_CNT_PH    => open,
        CRDT_DOWN_CNT_NPH   => open,
        CRDT_DOWN_CNT_CPLH  => open,
        CRDT_DOWN_CNT_PD    => open,
        CRDT_DOWN_CNT_NPD   => open,
        CRDT_DOWN_CNT_CPLD  => open,

        CRDT_UP_INIT_DONE   => '0',
        CRDT_UP_UPDATE      => open,
        CRDT_UP_CNT_PH      => open,
        CRDT_UP_CNT_NPH     => open,
        CRDT_UP_CNT_CPLH    => open,
        CRDT_UP_CNT_PD      => open,
        CRDT_UP_CNT_NPD     => open,
        CRDT_UP_CNT_CPLD    => open,

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

        CQ_MFB_DATA         => CQ_MFB_DATA(0),
        CQ_MFB_META         => CQ_MFB_META(0),
        CQ_MFB_SOF          => CQ_MFB_SOF(0),
        CQ_MFB_EOF          => CQ_MFB_EOF(0),
        CQ_MFB_SOF_POS      => CQ_MFB_SOF_POS(0),
        CQ_MFB_EOF_POS      => CQ_MFB_EOF_POS(0),
        CQ_MFB_SRC_RDY      => CQ_MFB_SRC_RDY(0),
        CQ_MFB_DST_RDY      => CQ_MFB_DST_RDY(0),

        RC_MFB_DATA         => RC_MFB_DATA(0),
        RC_MFB_META         => RC_MFB_META(0),
        RC_MFB_SOF          => RC_MFB_SOF(0),
        RC_MFB_EOF          => RC_MFB_EOF(0),
        RC_MFB_SOF_POS      => RC_MFB_SOF_POS(0),
        RC_MFB_EOF_POS      => RC_MFB_EOF_POS(0),
        RC_MFB_SRC_RDY      => RC_MFB_SRC_RDY(0),
        RC_MFB_DST_RDY      => RC_MFB_DST_RDY(0),

        CC_MFB_DATA         => CC_MFB_DATA(0),
        CC_MFB_META         => CC_MFB_META(0),
        CC_MFB_SOF          => CC_MFB_SOF(0),
        CC_MFB_EOF          => CC_MFB_EOF(0),
        CC_MFB_SOF_POS      => CC_MFB_SOF_POS(0),
        CC_MFB_EOF_POS      => CC_MFB_EOF_POS(0),
        CC_MFB_SRC_RDY      => CC_MFB_SRC_RDY(0),
        CC_MFB_DST_RDY      => CC_MFB_DST_RDY(0),

        RQ_MFB_DATA         => RQ_MFB_DATA(0),
        RQ_MFB_META         => RQ_MFB_META(0),
        RQ_MFB_SOF          => RQ_MFB_SOF(0),
        RQ_MFB_EOF          => RQ_MFB_EOF(0),
        RQ_MFB_SOF_POS      => RQ_MFB_SOF_POS(0),
        RQ_MFB_EOF_POS      => RQ_MFB_EOF_POS(0),
        RQ_MFB_SRC_RDY      => RQ_MFB_SRC_RDY(0),
        RQ_MFB_DST_RDY      => RQ_MFB_DST_RDY(0)
    );

    -- =========================================================================
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_rst_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => RESET_WIDTH+1
    )
    port map (
        CLK       => pcie_clk(0),
        ASYNC_RST => pcie_reset_status(0),
        OUT_RST   => pcie_rst(0)
    );

    PCIE_USER_CLK(0)   <= pcie_clk(0);
    PCIE_USER_RESET(0) <= pcie_rst(0)(RESET_WIDTH+1-1 downto 1);

    -- =========================================================================
    --  PCIE CONFIGURATION REGISTERS
    -- =========================================================================

    process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            pcie_link_up_reg(0) <= pcie_link_up_comb(0);
            PCIE_LINK_UP(0)     <= pcie_link_up_reg(0);
        end if;
    end process;

    PCIE_MPS(0)            <= "010"; -- 512B
    PCIE_MRRS(0)           <= "010"; -- 512B
    PCIE_EXT_TAG_EN(0)     <= '1';
    PCIE_RCB_SIZE(0)       <= '0';
    PCIE_10B_TAG_REQ_EN(0) <= '0';

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    -- Interface conversion (Intel CEB <=> Xilinx CFG_EXT)
    cfg_ext_reg_p : process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            cfg_ext_register(0)   <= pcie_ceb_addr(11 downto 2);
            cfg_ext_write_be(0)   <= pcie_ceb_wr;
            cfg_ext_write_data(0) <= pcie_ceb_dout;
        end if;
    end process;

    cfg_ext_vld_reg_p : process (pcie_clk(0))
    begin
        if (rising_edge(pcie_clk(0))) then
            if (pcie_rst(0)(0) = '1' or pcie_ceb_ack = '1') then
                cfg_ext_write(0) <= '0';
                cfg_ext_read(0)  <= '0';
            else
                cfg_ext_write(0) <= (or pcie_ceb_wr) and pcie_ceb_req;
                cfg_ext_read(0)  <= (nor pcie_ceb_wr) and pcie_ceb_req;
            end if;
        end if;
    end process;

    pcie_ceb_din <= cfg_ext_read_data(0);
    pcie_ceb_ack <= cfg_ext_read_dv(0) or cfg_ext_write(0);

    -- Device Tree ROM
    pci_ext_cap_i: entity work.PCI_EXT_CAP
    generic map(
        ENDPOINT_ID            => 0,
        ENDPOINT_ID_ENABLE     => true,
        DEVICE_TREE_ENABLE     => true,
        VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
        VSEC_NEXT_POINTER      => 16#000#,
        CARD_ID_WIDTH          => CARD_ID_WIDTH,
        CFG_EXT_READ_DV_HOTFIX => false
    )
    port map(
        CLK                    => pcie_clk(0),
        CARD_ID                => CARD_ID(0),
        CFG_EXT_READ           => cfg_ext_read(0),
        CFG_EXT_WRITE          => cfg_ext_write(0),
        CFG_EXT_REGISTER       => cfg_ext_register(0),
        CFG_EXT_FUNCTION       => (others => '0'),
        CFG_EXT_WRITE_DATA     => cfg_ext_write_data(0),
        CFG_EXT_WRITE_BE       => cfg_ext_write_be(0),
        CFG_EXT_READ_DATA      => cfg_ext_read_data(0),
        CFG_EXT_READ_DV        => cfg_ext_read_dv(0)
    );

end architecture;
