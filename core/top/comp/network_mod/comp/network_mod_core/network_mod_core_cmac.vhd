-- network_mod_core_cmac.vhd: Core of the Network module with Xilinx CMAC IP.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

architecture CMAC of NETWORK_MOD_CORE is

    -- =========================================================================
    --  COMPONENTS
    -- =========================================================================

    component cmac_eth_1x100g
    port (
        --Vivado 2019.1 and older
        --gt0_rxp_in                     : in std_logic;
        --gt0_rxn_in                     : in std_logic;
        --gt1_rxp_in                     : in std_logic;
        --gt1_rxn_in                     : in std_logic;
        --gt2_rxp_in                     : in std_logic;
        --gt2_rxn_in                     : in std_logic;
        --gt3_rxp_in                     : in std_logic;
        --gt3_rxn_in                     : in std_logic;

        --gt0_txp_out                    : out std_logic;
        --gt0_txn_out                    : out std_logic;
        --gt1_txp_out                    : out std_logic;
        --gt1_txn_out                    : out std_logic;
        --gt2_txp_out                    : out std_logic;
        --gt2_txn_out                    : out std_logic;
        --gt3_txp_out                    : out std_logic;
        --gt3_txn_out                    : out std_logic;

        --Vivado 2022.1 and newer
        gt_rxp_in  : in STD_LOGIC_VECTOR ( 3 downto 0 );
        gt_rxn_in  : in STD_LOGIC_VECTOR ( 3 downto 0 );
        gt_txp_out : out STD_LOGIC_VECTOR ( 3 downto 0 );
        gt_txn_out : out STD_LOGIC_VECTOR ( 3 downto 0 );

        gt_txusrclk2                   : out std_logic;
        gt_rxusrclk2                   : out std_logic;
        gt_loopback_in                 : in std_logic_vector(11 downto 0);
        gt_eyescanreset                : in std_logic_vector(3 downto 0);
        gt_eyescantrigger              : in std_logic_vector(3 downto 0);
        gt_rxcdrhold                   : in std_logic_vector(3 downto 0);
        gt_rxpolarity                  : in std_logic_vector(3 downto 0);
        gt_rxrate                      : in std_logic_vector(11 downto 0);
        gt_txdiffctrl                  : in std_logic_vector(19 downto 0);
        gt_txpolarity                  : in std_logic_vector(3 downto 0);
        gt_txinhibit                   : in std_logic_vector(3 downto 0);
        gt_txpostcursor                : in std_logic_vector(19 downto 0);
        gt_txprbsforceerr              : in std_logic_vector(3 downto 0);
        gt_txprecursor                 : in std_logic_vector(19 downto 0);
        gt_eyescandataerror            : out std_logic_vector(3 downto 0);
        gt_ref_clk_out                 : out std_logic;
        gt_rxrecclkout                 : out std_logic_vector(3 downto 0);
        gt_powergoodout                : out std_logic_vector(3 downto 0);
        gt_txbufstatus                 : out std_logic_vector(7 downto 0);
        gt_rxdfelpmreset               : in std_logic_vector(3 downto 0);
        gt_rxlpmen                     : in std_logic_vector(3 downto 0);
        gt_rxprbscntreset              : in std_logic_vector(3 downto 0);
        gt_rxprbserr                   : out std_logic_vector(3 downto 0);
        gt_rxprbssel                   : in std_logic_vector(15 downto 0);
        gt_rxresetdone                 : out std_logic_vector(3 downto 0);
        gt_txprbssel                   : in std_logic_vector(15 downto 0);
        gt_txresetdone                 : out std_logic_vector(3 downto 0);
        gt_rxbufstatus                 : out std_logic_vector(11 downto 0);
        gtwiz_reset_tx_datapath        : in std_logic;
        gtwiz_reset_rx_datapath        : in std_logic;

        gt_txpippmen                   : in std_logic_vector(3 downto 0);
        gt_txpippmsel                  : in std_logic_vector(3 downto 0);

        gt_drpclk                      : in std_logic;
        gt0_drpdo                      : out std_logic_vector(15 downto 0);
        gt0_drprdy                     : out std_logic;
        gt0_drpen                      : in std_logic;
        gt0_drpwe                      : in std_logic;
        gt0_drpaddr                    : in std_logic_vector(9 downto 0);
        gt0_drpdi                      : in std_logic_vector(15 downto 0);
        gt1_drpdo                      : out std_logic_vector(15 downto 0);
        gt1_drprdy                     : out std_logic;
        gt1_drpen                      : in std_logic;
        gt1_drpwe                      : in std_logic;
        gt1_drpaddr                    : in std_logic_vector(9 downto 0);
        gt1_drpdi                      : in std_logic_vector(15 downto 0);
        gt2_drpdo                      : out std_logic_vector(15 downto 0);
        gt2_drprdy                     : out std_logic;
        gt2_drpen                      : in std_logic;
        gt2_drpwe                      : in std_logic;
        gt2_drpaddr                    : in std_logic_vector(9 downto 0);
        gt2_drpdi                      : in std_logic_vector(15 downto 0);
        gt3_drpdo                      : out std_logic_vector(15 downto 0);
        gt3_drprdy                     : out std_logic;
        gt3_drpen                      : in std_logic;
        gt3_drpwe                      : in std_logic;
        gt3_drpaddr                    : in std_logic_vector(9 downto 0);
        gt3_drpdi                      : in std_logic_vector(15 downto 0);
        --
        ctl_tx_rsfec_enable            : in std_logic;
        ctl_rx_rsfec_enable            : in std_logic;
        ctl_rsfec_ieee_error_indication_mode : in std_logic;
        ctl_rx_rsfec_enable_correction : in std_logic;
        ctl_rx_rsfec_enable_indication : in std_logic;
        stat_rx_rsfec_am_lock0         : out std_logic;
        stat_rx_rsfec_am_lock1         : out std_logic;
        stat_rx_rsfec_am_lock2         : out std_logic;
        stat_rx_rsfec_am_lock3         : out std_logic;
        stat_rx_rsfec_corrected_cw_inc : out std_logic;
        stat_rx_rsfec_cw_inc           : out std_logic;
        stat_rx_rsfec_err_count0_inc   : out std_logic_vector(2 downto 0);
        stat_rx_rsfec_err_count1_inc   : out std_logic_vector(2 downto 0);
        stat_rx_rsfec_err_count2_inc   : out std_logic_vector(2 downto 0);
        stat_rx_rsfec_err_count3_inc   : out std_logic_vector(2 downto 0);
        stat_rx_rsfec_hi_ser           : out std_logic;
        stat_rx_rsfec_lane_alignment_status : out std_logic;
        stat_rx_rsfec_lane_fill_0      : out std_logic_vector(13 downto 0);
        stat_rx_rsfec_lane_fill_1      : out std_logic_vector(13 downto 0);
        stat_rx_rsfec_lane_fill_2      : out std_logic_vector(13 downto 0);
        stat_rx_rsfec_lane_fill_3      : out std_logic_vector(13 downto 0);
        stat_rx_rsfec_lane_mapping     : out std_logic_vector(7 downto 0);
        stat_rx_rsfec_uncorrected_cw_inc : out std_logic;
        --
        sys_reset                      : in std_logic;
        gt_ref_clk_p                   : in std_logic;
        gt_ref_clk_n                   : in std_logic;
        init_clk                       : in std_logic;
        common0_drpaddr                : in std_logic_vector(15 downto 0);
        common0_drpdi                  : in std_logic_vector(15 downto 0);
        common0_drpwe                  : in std_logic;
        common0_drpen                  : in std_logic;
        common0_drprdy                 : out std_logic;
        common0_drpdo                  : out std_logic_vector(15 downto 0);

        rx_dataout0                    : out std_logic_vector(127 downto 0);
        rx_dataout1                    : out std_logic_vector(127 downto 0);
        rx_dataout2                    : out std_logic_vector(127 downto 0);
        rx_dataout3                    : out std_logic_vector(127 downto 0);
        rx_enaout0                     : out std_logic;
        rx_enaout1                     : out std_logic;
        rx_enaout2                     : out std_logic;
        rx_enaout3                     : out std_logic;
        rx_eopout0                     : out std_logic;
        rx_eopout1                     : out std_logic;
        rx_eopout2                     : out std_logic;
        rx_eopout3                     : out std_logic;
        rx_errout0                     : out std_logic;
        rx_errout1                     : out std_logic;
        rx_errout2                     : out std_logic;
        rx_errout3                     : out std_logic;
        rx_mtyout0                     : out std_logic_vector(3 downto 0);
        rx_mtyout1                     : out std_logic_vector(3 downto 0);
        rx_mtyout2                     : out std_logic_vector(3 downto 0);
        rx_mtyout3                     : out std_logic_vector(3 downto 0);
        rx_sopout0                     : out std_logic;
        rx_sopout1                     : out std_logic;
        rx_sopout2                     : out std_logic;
        rx_sopout3                     : out std_logic;

        rx_otn_bip8_0                  : out std_logic_vector(7 downto 0);
        rx_otn_bip8_1                  : out std_logic_vector(7 downto 0);
        rx_otn_bip8_2                  : out std_logic_vector(7 downto 0);
        rx_otn_bip8_3                  : out std_logic_vector(7 downto 0);
        rx_otn_bip8_4                  : out std_logic_vector(7 downto 0);
        rx_otn_data_0                  : out std_logic_vector(65 downto 0);
        rx_otn_data_1                  : out std_logic_vector(65 downto 0);
        rx_otn_data_2                  : out std_logic_vector(65 downto 0);
        rx_otn_data_3                  : out std_logic_vector(65 downto 0);
        rx_otn_data_4                  : out std_logic_vector(65 downto 0);
        rx_otn_ena                     : out std_logic;
        rx_otn_lane0                   : out std_logic;
        rx_otn_vlmarker                : out std_logic;
        rx_preambleout                 : out std_logic_vector(55 downto 0);

        usr_rx_reset                   : out std_logic;

        stat_rx_aligned                : out std_logic;
        stat_rx_aligned_err            : out std_logic;
        stat_rx_bad_code               : out std_logic_vector(2 downto 0);
        stat_rx_bad_fcs                : out std_logic_vector(2 downto 0);
        stat_rx_bad_preamble           : out std_logic;
        stat_rx_bad_sfd                : out std_logic;

        stat_rx_bip_err_0              : out std_logic;
        stat_rx_bip_err_1              : out std_logic;
        stat_rx_bip_err_10             : out std_logic;
        stat_rx_bip_err_11             : out std_logic;
        stat_rx_bip_err_12             : out std_logic;
        stat_rx_bip_err_13             : out std_logic;
        stat_rx_bip_err_14             : out std_logic;
        stat_rx_bip_err_15             : out std_logic;
        stat_rx_bip_err_16             : out std_logic;
        stat_rx_bip_err_17             : out std_logic;
        stat_rx_bip_err_18             : out std_logic;
        stat_rx_bip_err_19             : out std_logic;
        stat_rx_bip_err_2              : out std_logic;
        stat_rx_bip_err_3              : out std_logic;
        stat_rx_bip_err_4              : out std_logic;
        stat_rx_bip_err_5              : out std_logic;
        stat_rx_bip_err_6              : out std_logic;
        stat_rx_bip_err_7              : out std_logic;
        stat_rx_bip_err_8              : out std_logic;
        stat_rx_bip_err_9              : out std_logic;

        stat_rx_block_lock             : out std_logic_vector(19 downto 0);
        stat_rx_broadcast              : out std_logic;
        stat_rx_fragment               : out std_logic_vector(2 downto 0);

        stat_rx_framing_err_0          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_1          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_10         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_11         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_12         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_13         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_14         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_15         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_16         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_17         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_18         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_19         : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_2          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_3          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_4          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_5          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_6          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_7          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_8          : out std_logic_vector(1 downto 0);
        stat_rx_framing_err_9          : out std_logic_vector(1 downto 0);

        stat_rx_framing_err_valid_0    : out std_logic;
        stat_rx_framing_err_valid_1    : out std_logic;
        stat_rx_framing_err_valid_10   : out std_logic;
        stat_rx_framing_err_valid_11   : out std_logic;
        stat_rx_framing_err_valid_12   : out std_logic;
        stat_rx_framing_err_valid_13   : out std_logic;
        stat_rx_framing_err_valid_14   : out std_logic;
        stat_rx_framing_err_valid_15   : out std_logic;
        stat_rx_framing_err_valid_16   : out std_logic;
        stat_rx_framing_err_valid_17   : out std_logic;
        stat_rx_framing_err_valid_18   : out std_logic;
        stat_rx_framing_err_valid_19   : out std_logic;
        stat_rx_framing_err_valid_2    : out std_logic;
        stat_rx_framing_err_valid_3    : out std_logic;
        stat_rx_framing_err_valid_4    : out std_logic;
        stat_rx_framing_err_valid_5    : out std_logic;
        stat_rx_framing_err_valid_6    : out std_logic;
        stat_rx_framing_err_valid_7    : out std_logic;
        stat_rx_framing_err_valid_8    : out std_logic;
        stat_rx_framing_err_valid_9    : out std_logic;

        stat_rx_got_signal_os          : out std_logic;
        stat_rx_hi_ber                 : out std_logic;
        stat_rx_inrangeerr             : out std_logic;
        stat_rx_internal_local_fault   : out std_logic;
        stat_rx_jabber                 : out std_logic;
        stat_rx_local_fault            : out std_logic;
        stat_rx_mf_err                 : out std_logic_vector(19 downto 0);
        stat_rx_mf_len_err             : out std_logic_vector(19 downto 0);
        stat_rx_mf_repeat_err          : out std_logic_vector(19 downto 0);
        stat_rx_misaligned             : out std_logic;
        stat_rx_multicast              : out std_logic;
        stat_rx_oversize               : out std_logic;

        stat_rx_packet_1024_1518_bytes : out std_logic;
        stat_rx_packet_128_255_bytes   : out std_logic;
        stat_rx_packet_1519_1522_bytes : out std_logic;
        stat_rx_packet_1523_1548_bytes : out std_logic;
        stat_rx_packet_1549_2047_bytes : out std_logic;
        stat_rx_packet_2048_4095_bytes : out std_logic;
        stat_rx_packet_256_511_bytes   : out std_logic;
        stat_rx_packet_4096_8191_bytes : out std_logic;
        stat_rx_packet_512_1023_bytes  : out std_logic;
        stat_rx_packet_64_bytes        : out std_logic;
        stat_rx_packet_65_127_bytes    : out std_logic;
        stat_rx_packet_8192_9215_bytes : out std_logic;
        stat_rx_packet_bad_fcs         : out std_logic;
        stat_rx_packet_large           : out std_logic;
        stat_rx_packet_small           : out std_logic_vector(2 downto 0);

        ctl_rx_enable                  : in std_logic;
        ctl_rx_force_resync            : in std_logic;
        ctl_rx_test_pattern            : in std_logic;

        core_rx_reset                  : in std_logic;
        rx_clk                         : in std_logic;

        stat_rx_received_local_fault   : out std_logic;
        stat_rx_remote_fault           : out std_logic;
        stat_rx_status                 : out std_logic;
        stat_rx_stomped_fcs            : out std_logic_vector(2 downto 0);
        stat_rx_synced                 : out std_logic_vector(19 downto 0);
        stat_rx_synced_err             : out std_logic_vector(19 downto 0);
        stat_rx_test_pattern_mismatch  : out std_logic_vector(2 downto 0);
        stat_rx_toolong                : out std_logic;
        stat_rx_total_bytes            : out std_logic_vector(6 downto 0);
        stat_rx_total_good_bytes       : out std_logic_vector(13 downto 0);
        stat_rx_total_good_packets     : out std_logic;
        stat_rx_total_packets          : out std_logic_vector(2 downto 0);
        stat_rx_truncated              : out std_logic;
        stat_rx_undersize              : out std_logic_vector(2 downto 0);
        stat_rx_unicast                : out std_logic;
        stat_rx_vlan                   : out std_logic;

        stat_rx_pcsl_demuxed           : out std_logic_vector(19 downto 0);
        stat_rx_pcsl_number_0          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_1          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_10         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_11         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_12         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_13         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_14         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_15         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_16         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_17         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_18         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_19         : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_2          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_3          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_4          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_5          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_6          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_7          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_8          : out std_logic_vector(4 downto 0);
        stat_rx_pcsl_number_9          : out std_logic_vector(4 downto 0);

        stat_tx_bad_fcs                : out std_logic;
        stat_tx_broadcast              : out std_logic;
        stat_tx_frame_error            : out std_logic;
        stat_tx_local_fault            : out std_logic;
        stat_tx_multicast              : out std_logic;

        stat_tx_packet_1024_1518_bytes : out std_logic;
        stat_tx_packet_128_255_bytes   : out std_logic;
        stat_tx_packet_1519_1522_bytes : out std_logic;
        stat_tx_packet_1523_1548_bytes : out std_logic;
        stat_tx_packet_1549_2047_bytes : out std_logic;
        stat_tx_packet_2048_4095_bytes : out std_logic;
        stat_tx_packet_256_511_bytes   : out std_logic;
        stat_tx_packet_4096_8191_bytes : out std_logic;
        stat_tx_packet_512_1023_bytes  : out std_logic;
        stat_tx_packet_64_bytes        : out std_logic;
        stat_tx_packet_65_127_bytes    : out std_logic;
        stat_tx_packet_8192_9215_bytes : out std_logic;
        stat_tx_packet_large           : out std_logic;
        stat_tx_packet_small           : out std_logic;

        stat_tx_total_bytes            : out std_logic_vector(5 downto 0);
        stat_tx_total_good_bytes       : out std_logic_vector(13 downto 0);
        stat_tx_total_good_packets     : out std_logic;
        stat_tx_total_packets          : out std_logic;
        stat_tx_unicast                : out std_logic;
        stat_tx_vlan                   : out std_logic;

        ctl_tx_enable                  : in std_logic;
        ctl_tx_send_idle               : in std_logic;
        ctl_tx_send_rfi                : in std_logic;
        ctl_tx_send_lfi                : in std_logic;
        ctl_tx_test_pattern            : in std_logic;

        core_tx_reset                  : in std_logic;

        tx_ovfout                      : out std_logic;
        tx_rdyout                      : out std_logic;
        tx_unfout                      : out std_logic;
        tx_datain0                     : in std_logic_vector(127 downto 0);
        tx_datain1                     : in std_logic_vector(127 downto 0);
        tx_datain2                     : in std_logic_vector(127 downto 0);
        tx_datain3                     : in std_logic_vector(127 downto 0);
        tx_enain0                      : in std_logic;
        tx_enain1                      : in std_logic;
        tx_enain2                      : in std_logic;
        tx_enain3                      : in std_logic;
        tx_eopin0                      : in std_logic;
        tx_eopin1                      : in std_logic;
        tx_eopin2                      : in std_logic;
        tx_eopin3                      : in std_logic;
        tx_errin0                      : in std_logic;
        tx_errin1                      : in std_logic;
        tx_errin2                      : in std_logic;
        tx_errin3                      : in std_logic;
        tx_mtyin0                      : in std_logic_vector(3 downto 0);
        tx_mtyin1                      : in std_logic_vector(3 downto 0);
        tx_mtyin2                      : in std_logic_vector(3 downto 0);
        tx_mtyin3                      : in std_logic_vector(3 downto 0);
        tx_sopin0                      : in std_logic;
        tx_sopin1                      : in std_logic;
        tx_sopin2                      : in std_logic;
        tx_sopin3                      : in std_logic;
        tx_preamblein                  : in std_logic_vector(55 downto 0);
        --
        usr_tx_reset                   : out std_logic;
        core_drp_reset                 : in std_logic;
        drp_clk                        : in std_logic;
        drp_addr                       : in std_logic_vector(9 downto 0);
        drp_di                         : in std_logic_vector(15 downto 0);
        drp_en                         : in std_logic;
        drp_do                         : out std_logic_vector(15 downto 0);
        drp_rdy                        : out std_logic;
        drp_we                         : in std_logic
    );
    end component;

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================

    function speed_cap_f return std_logic_vector is
        variable speed_cap_v : std_logic_vector(15 downto 0);
    begin
        speed_cap_v := (others => '0');
        case ETH_PORT_SPEED is
            when 400 => speed_cap_v(15) := '1';
            when 200 => speed_cap_v(12) := '1';
            when 100 => speed_cap_v(9)  := '1';
            when 50  => speed_cap_v(3)  := '1';
            when 40  => speed_cap_v(8)  := '1';
            when 25  => speed_cap_v(11) := '1';
            when others => speed_cap_v(0)  := '1'; -- 10GE
        end case;
        return speed_cap_v;
    end function;

    constant DRP_IFS           : natural := 5;
    constant NUM_LANES         : natural := 20;
    constant PMA_LANES         : natural := LANES/ETH_PORT_CHAN;
    constant SPEED_CAP         : std_logic_vector(16-1 downto 0) := speed_cap_f;

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    signal cmac_rx_hi_ber          : std_logic;
    signal cmac_rx_block_lock      : std_logic_vector(NUM_LANES-1 downto 0);
    signal cmac_rx_status          : std_logic;
    signal mgmt_ber_count          : std_logic_vector(22-1 downto 0);
    signal mgmt_ber_count_clr      : std_logic;
    signal mgmt_blk_err_cntr       : std_logic_vector(22-1 downto 0);
    signal mgmt_blk_err_clr        : std_logic;
    signal mgmt_pcs_reset          : std_logic;
    signal cmac_rx_aligned         : std_logic;
    signal mgmt_bip_err_cntrs      : std_logic_vector(NUM_LANES*16-1 downto 0);
    signal mgmt_bip_err_clr        : std_logic_vector(NUM_LANES-1 downto 0);
    signal cmac_rx_pcsl_number     : std_logic_vector(NUM_LANES*5-1 downto 0);
    signal cmac_rx_synced          : std_logic_vector(NUM_LANES-1 downto 0);
    signal mgmt_pma_loopback       : std_logic;
    signal mgmt_pma_rem_loopback   : std_logic;  
    signal mgmt_pcs_rev_loopback   : std_logic;
    signal mgmt_pma_reset          : std_logic;
    signal mgmt_gt_precursor       : std_logic_vector(32-1 downto 0);
    signal mgmt_gt_postcursor      : std_logic_vector(32-1 downto 0);
    signal mgmt_gt_txdiffctrl      : std_logic_vector(32-1 downto 0);
    signal mgmt_fec_tx_en          : std_logic;
    signal mgmt_fec_rx_en          : std_logic;
    signal mgmt_fec_cor_en         : std_logic;
    signal mgmt_fec_ind_en         : std_logic;
    signal cmac_fec_am_lock        : std_logic_vector(4-1 downto 0);
    signal cmac_fec_hi_ser         : std_logic;
    signal cmac_fec_algn_stat      : std_logic;
    signal cmac_fec_lane_map       : std_logic_vector(8-1 downto 0);
    signal mgmt_sym_err            : std_logic_vector(4*32-1 downto 0);
    signal mgmt_sym_err_clr        : std_logic_vector(4-1 downto 0);
    signal mgmt_cor_err            : std_logic_vector(32-1 downto 0);
    signal mgmt_cor_err_clr        : std_logic;
    signal mgmt_uncor_err          : std_logic_vector(32-1 downto 0);
    signal mgmt_uncor_err_clr      : std_logic;
    signal mgmt_pcs_control_i      : std_logic_vector(16-1 downto 0);
    signal mgmt_pcs_control        : std_logic_vector(16-1 downto 0);
    signal mgmt_pcs_status         : std_logic_vector(16-1 downto 0);

    signal mgmt_drpdo              : std_logic_vector(16-1 downto 0);
    signal mgmt_drprdy             : std_logic;
    signal mgmt_drpen              : std_logic;
    signal mgmt_drpwe              : std_logic;
    signal mgmt_drpaddr            : std_logic_vector(16-1 downto 0);
    signal mgmt_drpdi              : std_logic_vector(16-1 downto 0);
    signal mgmt_drpsel             : std_logic_vector(4-1 downto 0);

    signal cmac_drpdo              : slv_array_t(DRP_IFS-1 downto 0)(16-1 downto 0);
    signal cmac_drprdy             : std_logic_vector(DRP_IFS-1 downto 0);
    signal cmac_drpen              : std_logic_vector(DRP_IFS-1 downto 0);
    signal cmac_drpwe              : std_logic_vector(DRP_IFS-1 downto 0);
    signal cmac_drpaddr            : slv_array_t(DRP_IFS-1 downto 0)(16-1 downto 0);
    signal cmac_drpdi              : slv_array_t(DRP_IFS-1 downto 0)(16-1 downto 0);

    signal cmac_reset              : std_logic;
    signal ber_count_clr           : std_logic;
    signal cmac_rx_framing_err_vld : std_logic_vector(NUM_LANES-1 downto 0);
    signal cmac_rx_framing_err     : slv_array_t(NUM_LANES-1 downto 0)(2-1 downto 0);
    signal framing_err_sum         : unsigned(6-1 downto 0);
    signal ber_count               : unsigned(22-1 downto 0);
    signal ber_count_max           : std_logic;

    signal cmac_rx_bad_code        : std_logic_vector(3-1 downto 0);
    signal blk_err_clr             : std_logic;
    signal blk_err_cntr            : unsigned(22-1 downto 0);
    signal blk_err_cntr_max        : std_logic;

    signal cmac_rx_bip_err         : std_logic_vector(NUM_LANES-1 downto 0);
    signal bip_err_clr             : std_logic_vector(NUM_LANES-1 downto 0);
    signal bip_err_cntr            : u_array_t(NUM_LANES-1 downto 0)(16-1 downto 0);
    signal bip_err_cntr_max        : std_logic_vector(NUM_LANES-1 downto 0);

    signal cmac_fec_tx_en          : std_logic;
    signal cmac_fec_rx_en          : std_logic;
    signal cmac_fec_cor_en         : std_logic;
    signal cmac_fec_ind_en         : std_logic;

    signal cmac_fec_err_inc        : slv_array_t(4-1 downto 0)(3-1 downto 0);
    signal sym_err_cnt_clr         : std_logic_vector(4-1 downto 0);
    signal sym_err_cnt             : u_array_t(4-1 downto 0)(32-1 downto 0);
    signal sym_err_cnt_max         : std_logic_vector(4-1 downto 0);

    signal cmac_fec_cor_inc        : std_logic;
    signal cor_err_clr             : std_logic;
    signal cor_err_cnt             : unsigned(32-1 downto 0);
    signal cor_err_cnt_max         : std_logic;

    signal cmac_fec_uncor_inc      : std_logic;
    signal uncor_err_cnt_clr       : std_logic;
    signal uncor_err_cnt           : unsigned(32-1 downto 0);
    signal uncor_err_cnt_max       : std_logic;

    signal cmac_gt_tx_clk_322m     : std_logic;
    signal cmac_gt_rx_clk_322m     : std_logic;
    signal cmac_gt_pwrgood         : std_logic_vector(4-1 downto 0);
    signal cmac_rst_async          : std_logic;
    signal cmac_clk_322m           : std_logic;
    signal cmac_rst_322m           : std_logic;
    signal cmac_gt_loopback        : std_logic_vector(12-1 downto 0);
    signal gt_rxpolarity           : std_logic_vector(4-1 downto 0);
    signal gt_txpolarity           : std_logic_vector(4-1 downto 0);
    signal cmac_gt_rxpolarity      : std_logic_vector(4-1 downto 0);
    signal cmac_gt_txpolarity      : std_logic_vector(4-1 downto 0);

    signal cmac_rx_local_fault     : std_logic;
    signal cmac_rx_remote_fault    : std_logic;
    signal cmac_rx_local_fault_int : std_logic;
    signal cmac_tx_local_fault     : std_logic;
    signal rx_link_cnt             : unsigned(25-1 downto 0);
    signal rx_link_rst             : std_logic;
    signal link_up_cntr            : unsigned(25 downto 0);
    signal cmac_reset_rx_datapath  : std_logic;

    signal cmac_rx_lbus_data       : slv_array_t(4-1 downto 0)(128-1 downto 0);
    signal cmac_rx_lbus_ena        : std_logic_vector(4-1 downto 0);
    signal cmac_rx_lbus_eop        : std_logic_vector(4-1 downto 0);
    signal cmac_rx_lbus_err        : std_logic_vector(4-1 downto 0);
    signal cmac_rx_lbus_mty        : slv_array_t(4-1 downto 0)(4-1 downto 0);
    signal cmac_rx_lbus_sop        : std_logic_vector(4-1 downto 0);

    signal cmac_tx_lbus_data       : slv_array_t(4-1 downto 0)(128-1 downto 0);
    signal cmac_tx_lbus_ena        : std_logic_vector(4-1 downto 0);
    signal cmac_tx_lbus_eop        : std_logic_vector(4-1 downto 0);
    signal cmac_tx_lbus_err        : std_logic_vector(4-1 downto 0);
    signal cmac_tx_lbus_mty        : slv_array_t(4-1 downto 0)(4-1 downto 0);
    signal cmac_tx_lbus_sop        : std_logic_vector(4-1 downto 0);
    signal cmac_tx_lbus_rdy        : std_logic;

begin

    assert (ETH_PORT_CHAN = 1)
        report "NETWORK_MOD_CORE: Xilinx CMAC IP support only ETH_PORT_CHAN=1!"
        severity failure;
    assert (ETH_PORT_SPEED = 100)
        report "NETWORK_MOD_CORE: Xilinx CMAC IP support only ETH_PORT_SPEED=100!"
        severity failure;

    mgmt_i : entity work.mgmt
    generic map (
        NUM_LANES           => NUM_LANES,
        PMA_LANES           => PMA_LANES,
        SPEED               => ETH_PORT_SPEED,
        SPEED_CAP           => SPEED_CAP,
        RSFEC_ABLE          => '1',
        PMA_PRECURSOR_INIT  => X"000" & GTY_TX_EQ(3*20-1 downto 2*20),  
        PMA_POSTCURSOR_INIT => X"000" & GTY_TX_EQ(2*20-1 downto 1*20),
        PMA_DRIVE_INIT      => X"000" & GTY_TX_EQ(1*20-1 downto 0*20),   
        DEVICE              => DEVICE
    )
    port map (
        RESET         => MI_RESET_PHY,
        MI_CLK        => MI_CLK_PHY,
        MI_DWR        => MI_DWR_PHY,
        MI_ADDR       => MI_ADDR_PHY,
        MI_RD         => MI_RD_PHY,
        MI_WR         => MI_WR_PHY,
        MI_BE         => MI_BE_PHY,
        MI_DRD        => MI_DRD_PHY,
        MI_ARDY       => MI_ARDY_PHY,
        MI_DRDY       => MI_DRDY_PHY,
        -- PCS status
        HI_BER        => cmac_rx_hi_ber,
        BLK_LOCK      => cmac_rx_block_lock,
        LINKSTATUS    => cmac_rx_status,
        BER_COUNT     => mgmt_ber_count,
        BER_COUNT_CLR => mgmt_ber_count_clr,
        BLK_ERR_CNTR  => mgmt_blk_err_cntr,
        BLK_ERR_CLR   => mgmt_blk_err_clr,
        SCR_BYPASS    => open,
        PCS_RESET     => mgmt_pcs_reset,
        PCS_LPBCK     => open,
        PCS_CONTROL   => mgmt_pcs_control,
        PCS_CONTROL_I => mgmt_pcs_control_i,
        PCS_STATUS    => mgmt_pcs_status,
        -- PCS Lane align
        ALGN_LOCKED   => cmac_rx_aligned,
        BIP_ERR_CNTRS => mgmt_bip_err_cntrs,
        BIP_ERR_CLR   => mgmt_bip_err_clr,
        LANE_MAP      => cmac_rx_pcsl_number,
        LANE_ALIGN    => cmac_rx_synced,
        -- PMA & PMD status/control
        PMA_LOPWR     => open,
        PMA_LPBCK     => mgmt_pma_loopback,
        PMA_REM_LPBCK => mgmt_pma_rem_loopback,      
        PMA_RESET     => mgmt_pma_reset,
        PMA_RETUNE    => open,
        PMA_CONTROL   => open,
        PMA_STATUS    => (others => '0'),
        PMA_PTRN_EN   => open,
        PMA_TX_DIS    => open,
        PMA_RX_OK     => (others => '1'),
        PMD_SIG_DET   => (others => '1'), --TODO
        PMA_PRECURSOR => mgmt_gt_precursor,
        PMA_POSTCURSOR=> mgmt_gt_postcursor,
        PMA_DRIVE     => mgmt_gt_txdiffctrl,
        -- RS-FEC status/control
        FEC_TX_EN         => mgmt_fec_tx_en,
        FEC_RX_EN         => mgmt_fec_rx_en,
        FEC_COR_EN        => mgmt_fec_cor_en,
        FEC_IND_EN        => mgmt_fec_ind_en,
        FEC_AM_LOCK       => cmac_fec_am_lock,
        FEC_HI_SER        => cmac_fec_hi_ser,
        FEC_ALGN_STAT     => cmac_fec_algn_stat,
        FEC_LANE_MAP      => cmac_fec_lane_map,
        FEC_SYM_ERR       => mgmt_sym_err,
        FEC_SYM_ERR_CLR   => mgmt_sym_err_clr,
        FEC_COR_ERR       => mgmt_cor_err,
        FEC_COR_ERR_CLR   => mgmt_cor_err_clr,
        FEC_UNCOR_ERR     => mgmt_uncor_err,
        FEC_UNCOR_ERR_CLR => mgmt_uncor_err_clr,
        -- FEC PCS stats
        FEC_TX_BIP        => (others => '0'),
        FEC_TX_LANE_MAP   => X"0013001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000",
        FEC_TX_BLK_LOCK   => (others => '1'), 
        FEC_TX_ALGN_STAT  => (others => '1'),
        -- DRP interface
        DRPCLK            => MI_CLK_PHY,
        DRPDO             => mgmt_drpdo,
        DRPRDY            => mgmt_drprdy,
        DRPEN             => mgmt_drpen,
        DRPWE             => mgmt_drpwe,
        DRPADDR           => mgmt_drpaddr,
        DRPDI             => mgmt_drpdi,
        DRPSEL            => mgmt_drpsel
    );

    mgmt_pcs_rev_loopback <= mgmt_pcs_control(0);

    -- MDIO reg 3.4000 (vendor specific PCS control readout)
    mgmt_pcs_control_i(15 downto 1) <= (others => '0');
    mgmt_pcs_control_i(0)           <= mgmt_pcs_rev_loopback; -- PCS reverse loopback active
    -- MDIO reg 3.4001 (vendor specific PCS status/abilities)
    mgmt_pcs_status(15 downto 1)    <= (others => '0');
    mgmt_pcs_status(0)              <= '1';        -- PCS reverse loopback ability supported

    -- DRP switch --------------------------------------------------------------
    process (all)
    begin
        mgmt_drpdo  <= cmac_drpdo(0);
        mgmt_drprdy <= cmac_drprdy(0);
        for i in 0 to DRP_IFS-1 loop
            cmac_drpdi(i)   <= mgmt_drpdi;
            cmac_drpaddr(i) <= mgmt_drpaddr;
            cmac_drpwe(i)   <= mgmt_drpwe;
            cmac_drpen(i)   <= '0';
            if (unsigned(mgmt_drpsel) = i) then
                mgmt_drpdo  <= cmac_drpdo(i);
                mgmt_drprdy <= cmac_drprdy(i);
                cmac_drpen(i) <= mgmt_drpen;
            end if;
        end loop;
    end process;

    -- PCS reset ---------------------------------------------------------------
    pcs_reset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => cmac_clk_322m,
        ASYNC_RST  => mgmt_pcs_reset,
        OUT_RST(0) => cmac_reset
    );

    -- BER counter -------------------------------------------------------------
    ber_count_clr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_ber_count_clr,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => ber_count_clr
    );

    process (all)
        variable v_framing_err_sum : unsigned(6-1 downto 0);
    begin
        v_framing_err_sum := (others => '0');
        for i in 0 to NUM_LANES-1 loop
            if (cmac_rx_framing_err_vld(i) = '1') then
                v_framing_err_sum := v_framing_err_sum + unsigned(cmac_rx_framing_err(i));
            end if;
        end loop;
        framing_err_sum <= v_framing_err_sum;
    end process;

    process (cmac_clk_322m)
    begin
        if (rising_edge(cmac_clk_322m)) then
            if (ber_count_clr = '1') then
                ber_count <= (others => '0');
            elsif (ber_count_max = '0') then
                ber_count <= ber_count + framing_err_sum;
            end if;
        end if;
    end process;

    ber_count_max <= and ber_count;
    mgmt_ber_count <= std_logic_vector(ber_count);

    -- BLK error counter -------------------------------------------------------
    blk_err_clr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_blk_err_clr,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => blk_err_clr
    );

    process (cmac_clk_322m)
    begin
        if (rising_edge(cmac_clk_322m)) then
            if (blk_err_clr = '1') then
                blk_err_cntr <= (others => '0');
            elsif (blk_err_cntr_max = '0') then
                blk_err_cntr <= blk_err_cntr + unsigned(cmac_rx_bad_code);
            end if;
        end if;
    end process;

    blk_err_cntr_max <= and blk_err_cntr;
    mgmt_blk_err_cntr <= std_logic_vector(blk_err_cntr);

    -- BIP error counter -------------------------------------------------------
    bip_err_g : for i in 0 to NUM_LANES-1 generate
        bip_err_clr_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => true
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => mgmt_bip_err_clr(i),

            BCLK     => cmac_clk_322m,
            BRST     => '0',
            BDATAOUT => bip_err_clr(i)
        );

        process (cmac_clk_322m)
        begin
            if (rising_edge(cmac_clk_322m)) then
                if (bip_err_clr(i) = '1') then
                    bip_err_cntr(i) <= (others => '0');
                elsif (bip_err_cntr_max(i) = '0' and cmac_rx_bip_err(i) = '1') then
                    bip_err_cntr(i) <= bip_err_cntr(i) + 1;
                end if;
            end if;
        end process;

        bip_err_cntr_max(i) <= and std_logic_vector(bip_err_cntr(i));
        mgmt_bip_err_cntrs((i+1)*16-1 downto i*16) <= std_logic_vector(bip_err_cntr(i));
    end generate;

    -- FEC enables -------------------------------------------------------------
    fec_tx_en_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_fec_tx_en,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => cmac_fec_tx_en
    );

    fec_rx_en_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_fec_rx_en,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => cmac_fec_rx_en
    );

    fec_cor_en_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_fec_cor_en,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => cmac_fec_cor_en
    );

    fec_ind_en_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_fec_ind_en,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => cmac_fec_ind_en
    );

    -- FEC symbolic error counters ---------------------------------------------
    sym_err_g : for i in 0 to 3 generate
        sym_err_clr_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => true
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => mgmt_sym_err_clr(i),

            BCLK     => cmac_clk_322m,
            BRST     => '0',
            BDATAOUT => sym_err_cnt_clr(i)
        );

        process (cmac_clk_322m)
        begin
            if (rising_edge(cmac_clk_322m)) then
                if (sym_err_cnt_clr(i) = '1' or cmac_rst_322m = '1') then
                    sym_err_cnt(i) <= (others => '0');
                elsif (sym_err_cnt_max(i) = '0') then
                    sym_err_cnt(i) <= sym_err_cnt(i) + unsigned(cmac_fec_err_inc(i));
                end if;
            end if;
        end process;

        sym_err_cnt_max(i) <= and sym_err_cnt(i);
        mgmt_sym_err((i+1)*32-1 downto i*32) <= std_logic_vector(sym_err_cnt(i));
    end generate;

    -- FEC cor err counter -----------------------------------------------------
    cor_err_clr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_cor_err_clr,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => cor_err_clr
    );

    process (cmac_clk_322m)
    begin
        if (rising_edge(cmac_clk_322m)) then
            if (cor_err_clr = '1' or cmac_rst_322m = '1') then
                cor_err_cnt <= (others => '0');
            elsif (cor_err_cnt_max = '0' and cmac_fec_cor_inc  = '1') then
                cor_err_cnt <= cor_err_cnt + 1;
            end if;
        end if;
    end process;

    cor_err_cnt_max <= and cor_err_cnt;
    mgmt_cor_err <= std_logic_vector(cor_err_cnt);

    -- FEC uncor err counter ---------------------------------------------------
    uncor_err_clr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map(
        IN_REG  => false,
        TWO_REG => true
    )
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => mgmt_uncor_err_clr,

        BCLK     => cmac_clk_322m,
        BRST     => '0',
        BDATAOUT => uncor_err_cnt_clr
    );

    process (cmac_clk_322m)
    begin
        if (rising_edge(cmac_clk_322m)) then
            if (uncor_err_cnt_clr = '1' or cmac_rst_322m = '1') then
                uncor_err_cnt <= (others => '0');
            elsif (uncor_err_cnt_max = '0' and cmac_fec_uncor_inc  = '1') then
                uncor_err_cnt <= uncor_err_cnt + 1;
            end if;
        end if;
    end process;

    uncor_err_cnt_max <= and uncor_err_cnt;
    mgmt_uncor_err <= std_logic_vector(uncor_err_cnt);

    -- =========================================================================
    -- The IP core
    -- =========================================================================

    cmac_clk_322m <= cmac_gt_tx_clk_322m;
    CLK_ETH <= cmac_clk_322m;
    
    -- CMAC reset
    cmac_rst_async <= RESET_ETH or (not (and cmac_gt_pwrgood));
   
    cmac_rst_322m_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG  => false,
        OUT_REG  => true,
        REPLICAS => 1
    )
    port map (
        CLK        => cmac_clk_322m,
        ASYNC_RST  => cmac_rst_async,
        OUT_RST(0) => cmac_rst_322m
    );

    -- NOTE: PMA reverse loopback is used instead of the Far end PCS loopback as it is easier to implement
    cmac_gt_loopback <= "010010010010" when (mgmt_pma_loopback = '1')     else -- Near end PMA loopback
                        "100100100100" when (mgmt_pma_rem_loopback = '1') or (mgmt_pcs_rev_loopback = '1') else -- Far end PMA loopback
                        "000000000000"; -- Normal operation
        
    -- Disable polarity swaps when loopback is active             
    gt_rxpolarity <= (others => '0') when cmac_gt_loopback(1) = '1' else LANE_RX_POLARITY;
    gt_txpolarity <= (others => '0') when cmac_gt_loopback(1) = '1' else LANE_TX_POLARITY;  

    rxpol_g: for i in LANE_RX_POLARITY'range generate
        rxpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => true
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => gt_rxpolarity(i),
            --
            BCLK     => cmac_gt_rx_clk_322m,
            BRST     => '0',
            BDATAOUT => cmac_gt_rxpolarity(i)
        );
    end generate;

    txpol_g: for i in LANE_TX_POLARITY'range generate
        rxpol_sync_i : entity work.ASYNC_OPEN_LOOP
        generic map(
            IN_REG  => false,
            TWO_REG => true
        )
        port map(
            ACLK     => '0',
            ARST     => '0',
            ADATAIN  => gt_txpolarity(i),
            --
            BCLK     => cmac_gt_tx_clk_322m,
            BRST     => '0',
            BDATAOUT => cmac_gt_txpolarity(i)
        );
    end generate;

    -- monitoring RX link state
    process(cmac_clk_322m)
    begin
        if rising_edge(cmac_clk_322m) then
            if (cmac_rx_local_fault = '0') or (rx_link_rst = '1') then
                -- link is up, clear the counter
                rx_link_cnt <= (others => '0');
            else
                -- link is down, increase the counter
                rx_link_cnt <= rx_link_cnt + 1;
            end if;
            -- when its last bit (~100ms) is set, reset the link
            rx_link_rst <= rx_link_cnt(25-1);
        end if;
    end process;

    cmac_reset_rx_datapath <= mgmt_pma_reset or rx_link_rst; --TODO

    process(cmac_clk_322m)
    begin
        if rising_edge(cmac_clk_322m) then
            if (cmac_rst_322m = '1') then
                TX_LINK_UP <= (others => '0');
            else
                TX_LINK_UP(0) <= not cmac_tx_local_fault;
            end if;
            if (cmac_rx_local_fault = '1') or (cmac_rx_remote_fault = '1') or (cmac_rx_status = '0') then
                link_up_cntr <= (others => '0');
            elsif link_up_cntr(link_up_cntr'high) = '0' then
                link_up_cntr <= link_up_cntr + 1;
            end if;
            RX_LINK_UP(0) <= link_up_cntr(link_up_cntr'high);
        end if;
    end process;

    cmac_eth_1x100g_i : cmac_eth_1x100g
    port map(
        --Vivado 2019.1 and older
        --gt0_rxp_in  => QSFP_RX_P(0),
        --gt0_rxn_in  => QSFP_RX_N(0),
        --gt1_rxp_in  => QSFP_RX_P(1),
        --gt1_rxn_in  => QSFP_RX_N(1),
        --gt2_rxp_in  => QSFP_RX_P(2),
        --gt2_rxn_in  => QSFP_RX_N(2),
        --gt3_rxp_in  => QSFP_RX_P(3),
        --gt3_rxn_in  => QSFP_RX_N(3),

        --gt0_txn_out => QSFP_TX_N(0),
        --gt0_txp_out => QSFP_TX_P(0),
        --gt1_txn_out => QSFP_TX_N(1),
        --gt1_txp_out => QSFP_TX_P(1),
        --gt2_txn_out => QSFP_TX_N(2),
        --gt2_txp_out => QSFP_TX_P(2),
        --gt3_txn_out => QSFP_TX_N(3),
        --gt3_txp_out => QSFP_TX_P(3),

        --Vivado 2022.1 and newer
        gt_rxp_in  => QSFP_RX_P,
        gt_rxn_in  => QSFP_RX_N,
        gt_txp_out => QSFP_TX_P,
        gt_txn_out => QSFP_TX_N,

        gt_txusrclk2   => cmac_gt_tx_clk_322m,
        gt_rxusrclk2   => cmac_gt_rx_clk_322m,
        gt_loopback_in => cmac_gt_loopback,

        gt_txpippmen   => (others => '0'),
        gt_txpippmsel  => (others => '0'),

        gt_eyescanreset   => (others => '0'),
        gt_eyescantrigger => (others => '0'),
        gt_rxcdrhold      => (others => '0'),
        gt_rxpolarity     => cmac_gt_rxpolarity,
        gt_rxrate         => (others => '0'),
        gt_txpolarity     => cmac_gt_txpolarity,
        gt_txinhibit      => (others => '0'),
        -- 
        gt_txdiffctrl     => mgmt_gt_txdiffctrl(19 downto 0),         
        gt_txpostcursor   => mgmt_gt_postcursor(19 downto 0),
        gt_txprecursor    => mgmt_gt_precursor(19 downto 0),
        --
        gt_txprbsforceerr => (others => '0'),         
        gt_eyescandataerror => open,
        gt_txbufstatus      => open,
        gt_rxdfelpmreset    => (others => '0'),
        gt_rxlpmen          => (others => '0'),
        gt_rxprbscntreset   => (others => '0'),
        gt_rxprbserr        => open,
        gt_rxprbssel        => (others => '0'),
        gt_rxresetdone      => open,
        gt_txprbssel        => (others => '0'),
        gt_txresetdone      => open, --TODO
        gt_rxbufstatus      => open,
        gt_drpclk   => MI_CLK_PHY,
        gt0_drpdo   => cmac_drpdo(0),
        gt0_drprdy  => cmac_drprdy(0),
        gt0_drpen   => cmac_drpen(0),
        gt0_drpwe   => cmac_drpwe(0),
        gt0_drpaddr => cmac_drpaddr(0)(9 downto 0),
        gt0_drpdi   => cmac_drpdi(0),
        gt1_drpdo   => cmac_drpdo(1),
        gt1_drprdy  => cmac_drprdy(1),
        gt1_drpen   => cmac_drpen(1),
        gt1_drpwe   => cmac_drpwe(1),
        gt1_drpaddr => cmac_drpaddr(1)(9 downto 0),
        gt1_drpdi   => cmac_drpdi(1),
        gt2_drpdo   => cmac_drpdo(2),
        gt2_drprdy  => cmac_drprdy(2),
        gt2_drpen   => cmac_drpen(2),
        gt2_drpwe   => cmac_drpwe(2),
        gt2_drpaddr => cmac_drpaddr(2)(9 downto 0),
        gt2_drpdi   => cmac_drpdi(2),
        gt3_drpdo   => cmac_drpdo(3),
        gt3_drprdy  => cmac_drprdy(3),
        gt3_drpen   => cmac_drpen(3),
        gt3_drpwe   => cmac_drpwe(3),
        gt3_drpaddr => cmac_drpaddr(3)(9 downto 0),
        gt3_drpdi   => cmac_drpdi(3),
        common0_drpaddr => (others => '0'),
        common0_drpdi => (others => '0'),
        common0_drpwe => '0',
        common0_drpen => '0',
        common0_drprdy => open,
        common0_drpdo => open,

        gt_rxrecclkout => open,
        gt_powergoodout=> cmac_gt_pwrgood,
        gt_ref_clk_out => open,
        gtwiz_reset_rx_datapath => cmac_reset_rx_datapath,
        gtwiz_reset_tx_datapath => mgmt_pma_reset,
        sys_reset      => MI_RESET_PHY,
        gt_ref_clk_p   => QSFP_REFCLK_P,
        gt_ref_clk_n   => QSFP_REFCLK_N,
        init_clk       => MI_CLK_PHY,

        rx_dataout0 => cmac_rx_lbus_data(0),
        rx_dataout1 => cmac_rx_lbus_data(1),
        rx_dataout2 => cmac_rx_lbus_data(2),
        rx_dataout3 => cmac_rx_lbus_data(3),
        rx_enaout0  => cmac_rx_lbus_ena(0),
        rx_enaout1  => cmac_rx_lbus_ena(1),
        rx_enaout2  => cmac_rx_lbus_ena(2),
        rx_enaout3  => cmac_rx_lbus_ena(3),
        rx_eopout0  => cmac_rx_lbus_eop(0),
        rx_eopout1  => cmac_rx_lbus_eop(1),
        rx_eopout2  => cmac_rx_lbus_eop(2),
        rx_eopout3  => cmac_rx_lbus_eop(3),
        rx_errout0  => cmac_rx_lbus_err(0),
        rx_errout1  => cmac_rx_lbus_err(1),
        rx_errout2  => cmac_rx_lbus_err(2),
        rx_errout3  => cmac_rx_lbus_err(3),
        rx_mtyout0  => cmac_rx_lbus_mty(0),
        rx_mtyout1  => cmac_rx_lbus_mty(1),
        rx_mtyout2  => cmac_rx_lbus_mty(2),
        rx_mtyout3  => cmac_rx_lbus_mty(3),
        rx_sopout0  => cmac_rx_lbus_sop(0),
        rx_sopout1  => cmac_rx_lbus_sop(1),
        rx_sopout2  => cmac_rx_lbus_sop(2),
        rx_sopout3  => cmac_rx_lbus_sop(3),

        rx_preambleout => open,
        usr_rx_reset   => open,

        stat_rx_aligned      => cmac_rx_aligned,
        stat_rx_aligned_err  => open,

        stat_rx_bad_code     => cmac_rx_bad_code,
        stat_rx_bad_fcs      => open,
        stat_rx_bad_preamble => open,
        stat_rx_bad_sfd      => open,

        stat_rx_bip_err_0  => cmac_rx_bip_err(0),
        stat_rx_bip_err_1  => cmac_rx_bip_err(1),
        stat_rx_bip_err_10 => cmac_rx_bip_err(10),
        stat_rx_bip_err_11 => cmac_rx_bip_err(11),
        stat_rx_bip_err_12 => cmac_rx_bip_err(12),
        stat_rx_bip_err_13 => cmac_rx_bip_err(13),
        stat_rx_bip_err_14 => cmac_rx_bip_err(14),
        stat_rx_bip_err_15 => cmac_rx_bip_err(15),
        stat_rx_bip_err_16 => cmac_rx_bip_err(16),
        stat_rx_bip_err_17 => cmac_rx_bip_err(17),
        stat_rx_bip_err_18 => cmac_rx_bip_err(18),
        stat_rx_bip_err_19 => cmac_rx_bip_err(19),
        stat_rx_bip_err_2  => cmac_rx_bip_err(2),
        stat_rx_bip_err_3  => cmac_rx_bip_err(3),
        stat_rx_bip_err_4  => cmac_rx_bip_err(4),
        stat_rx_bip_err_5  => cmac_rx_bip_err(5),
        stat_rx_bip_err_6  => cmac_rx_bip_err(6),
        stat_rx_bip_err_7  => cmac_rx_bip_err(7),
        stat_rx_bip_err_8  => cmac_rx_bip_err(8),
        stat_rx_bip_err_9  => cmac_rx_bip_err(9),

        stat_rx_block_lock => cmac_rx_block_lock,
        stat_rx_broadcast  => open,
        stat_rx_fragment   => open,

        stat_rx_framing_err_0  => cmac_rx_framing_err(0),
        stat_rx_framing_err_1  => cmac_rx_framing_err(1),
        stat_rx_framing_err_10 => cmac_rx_framing_err(10),
        stat_rx_framing_err_11 => cmac_rx_framing_err(11),
        stat_rx_framing_err_12 => cmac_rx_framing_err(12),
        stat_rx_framing_err_13 => cmac_rx_framing_err(13),
        stat_rx_framing_err_14 => cmac_rx_framing_err(14),
        stat_rx_framing_err_15 => cmac_rx_framing_err(15),
        stat_rx_framing_err_16 => cmac_rx_framing_err(16),
        stat_rx_framing_err_17 => cmac_rx_framing_err(17),
        stat_rx_framing_err_18 => cmac_rx_framing_err(18),
        stat_rx_framing_err_19 => cmac_rx_framing_err(19),
        stat_rx_framing_err_2  => cmac_rx_framing_err(2),
        stat_rx_framing_err_3  => cmac_rx_framing_err(3),
        stat_rx_framing_err_4  => cmac_rx_framing_err(4),
        stat_rx_framing_err_5  => cmac_rx_framing_err(5),
        stat_rx_framing_err_6  => cmac_rx_framing_err(6),
        stat_rx_framing_err_7  => cmac_rx_framing_err(7),
        stat_rx_framing_err_8  => cmac_rx_framing_err(8),
        stat_rx_framing_err_9  => cmac_rx_framing_err(9),

        stat_rx_framing_err_valid_0  => cmac_rx_framing_err_vld(0),
        stat_rx_framing_err_valid_1  => cmac_rx_framing_err_vld(1),
        stat_rx_framing_err_valid_10 => cmac_rx_framing_err_vld(10),
        stat_rx_framing_err_valid_11 => cmac_rx_framing_err_vld(11),
        stat_rx_framing_err_valid_12 => cmac_rx_framing_err_vld(12),
        stat_rx_framing_err_valid_13 => cmac_rx_framing_err_vld(13),
        stat_rx_framing_err_valid_14 => cmac_rx_framing_err_vld(14),
        stat_rx_framing_err_valid_15 => cmac_rx_framing_err_vld(15),
        stat_rx_framing_err_valid_16 => cmac_rx_framing_err_vld(16),
        stat_rx_framing_err_valid_17 => cmac_rx_framing_err_vld(17),
        stat_rx_framing_err_valid_18 => cmac_rx_framing_err_vld(18),
        stat_rx_framing_err_valid_19 => cmac_rx_framing_err_vld(19),
        stat_rx_framing_err_valid_2  => cmac_rx_framing_err_vld(2),
        stat_rx_framing_err_valid_3  => cmac_rx_framing_err_vld(3),
        stat_rx_framing_err_valid_4  => cmac_rx_framing_err_vld(4),
        stat_rx_framing_err_valid_5  => cmac_rx_framing_err_vld(5),
        stat_rx_framing_err_valid_6  => cmac_rx_framing_err_vld(6),
        stat_rx_framing_err_valid_7  => cmac_rx_framing_err_vld(7),
        stat_rx_framing_err_valid_8  => cmac_rx_framing_err_vld(8),
        stat_rx_framing_err_valid_9  => cmac_rx_framing_err_vld(9),

        stat_rx_got_signal_os        => open,
        stat_rx_hi_ber               => cmac_rx_hi_ber,
        stat_rx_inrangeerr           => open,
        stat_rx_internal_local_fault => cmac_rx_local_fault_int, -- high when the rx link is down or pattern generator on
        stat_rx_jabber               => open,
        stat_rx_local_fault          => cmac_rx_local_fault,
        stat_rx_mf_err               => open,
        stat_rx_mf_len_err           => open,
        stat_rx_mf_repeat_err        => open,
        stat_rx_misaligned           => open,
        stat_rx_multicast            => open,
        stat_rx_oversize             => open,

        stat_rx_packet_1024_1518_bytes => open,
        stat_rx_packet_128_255_bytes   => open,
        stat_rx_packet_1519_1522_bytes => open,
        stat_rx_packet_1523_1548_bytes => open,
        stat_rx_packet_1549_2047_bytes => open,
        stat_rx_packet_2048_4095_bytes => open,
        stat_rx_packet_256_511_bytes   => open,
        stat_rx_packet_4096_8191_bytes => open,
        stat_rx_packet_512_1023_bytes  => open,
        stat_rx_packet_64_bytes        => open,
        stat_rx_packet_65_127_bytes    => open,
        stat_rx_packet_8192_9215_bytes => open,
        stat_rx_packet_bad_fcs         => open,
        stat_rx_packet_large           => open,
        stat_rx_packet_small           => open,

        ctl_rx_enable       => '1',
        ctl_rx_force_resync => '0',
        ctl_rx_test_pattern => '0',

        core_rx_reset => cmac_reset,
        rx_clk        => cmac_clk_322m,

        stat_rx_received_local_fault  => open,
        stat_rx_remote_fault          => cmac_rx_remote_fault,
        stat_rx_status                => cmac_rx_status,
        stat_rx_stomped_fcs           => open,
        stat_rx_synced                => cmac_rx_synced,
        stat_rx_synced_err            => open,
        stat_rx_test_pattern_mismatch => open,
        stat_rx_toolong               => open,
        stat_rx_total_bytes           => open,
        stat_rx_total_good_bytes      => open,
        stat_rx_total_good_packets    => open,
        stat_rx_total_packets         => open,
        stat_rx_truncated             => open,
        stat_rx_undersize             => open,
        stat_rx_unicast               => open,
        stat_rx_vlan                  => open,

        stat_rx_pcsl_demuxed   => open,
        stat_rx_pcsl_number_0  => cmac_rx_pcsl_number((0+1)*5-1 downto 0*5),
        stat_rx_pcsl_number_1  => cmac_rx_pcsl_number((1+1)*5-1 downto 1*5),
        stat_rx_pcsl_number_10 => cmac_rx_pcsl_number((10+1)*5-1 downto 10*5),
        stat_rx_pcsl_number_11 => cmac_rx_pcsl_number((11+1)*5-1 downto 11*5),
        stat_rx_pcsl_number_12 => cmac_rx_pcsl_number((12+1)*5-1 downto 12*5),
        stat_rx_pcsl_number_13 => cmac_rx_pcsl_number((13+1)*5-1 downto 13*5),
        stat_rx_pcsl_number_14 => cmac_rx_pcsl_number((14+1)*5-1 downto 14*5),
        stat_rx_pcsl_number_15 => cmac_rx_pcsl_number((15+1)*5-1 downto 15*5),
        stat_rx_pcsl_number_16 => cmac_rx_pcsl_number((16+1)*5-1 downto 16*5),
        stat_rx_pcsl_number_17 => cmac_rx_pcsl_number((17+1)*5-1 downto 17*5),
        stat_rx_pcsl_number_18 => cmac_rx_pcsl_number((18+1)*5-1 downto 18*5),
        stat_rx_pcsl_number_19 => cmac_rx_pcsl_number((19+1)*5-1 downto 19*5),
        stat_rx_pcsl_number_2  => cmac_rx_pcsl_number((2+1)*5-1 downto 2*5),
        stat_rx_pcsl_number_3  => cmac_rx_pcsl_number((3+1)*5-1 downto 3*5),
        stat_rx_pcsl_number_4  => cmac_rx_pcsl_number((4+1)*5-1 downto 4*5),
        stat_rx_pcsl_number_5  => cmac_rx_pcsl_number((5+1)*5-1 downto 5*5),
        stat_rx_pcsl_number_6  => cmac_rx_pcsl_number((6+1)*5-1 downto 6*5),
        stat_rx_pcsl_number_7  => cmac_rx_pcsl_number((7+1)*5-1 downto 7*5),
        stat_rx_pcsl_number_8  => cmac_rx_pcsl_number((8+1)*5-1 downto 8*5),
        stat_rx_pcsl_number_9  => cmac_rx_pcsl_number((9+1)*5-1 downto 9*5),

        stat_tx_bad_fcs     => open,
        stat_tx_broadcast   => open,
        stat_tx_frame_error => open,
        stat_tx_local_fault => cmac_tx_local_fault,
        stat_tx_multicast   => open,

        stat_tx_packet_1024_1518_bytes => open,
        stat_tx_packet_128_255_bytes   => open,
        stat_tx_packet_1519_1522_bytes => open,
        stat_tx_packet_1523_1548_bytes => open,
        stat_tx_packet_1549_2047_bytes => open,
        stat_tx_packet_2048_4095_bytes => open,
        stat_tx_packet_256_511_bytes   => open,
        stat_tx_packet_4096_8191_bytes => open,
        stat_tx_packet_512_1023_bytes  => open,
        stat_tx_packet_64_bytes        => open,
        stat_tx_packet_65_127_bytes    => open,
        stat_tx_packet_8192_9215_bytes => open,
        stat_tx_packet_large           => open,
        stat_tx_packet_small           => open,

        stat_tx_total_bytes        => open,
        stat_tx_total_good_bytes   => open,
        stat_tx_total_good_packets => open,
        stat_tx_total_packets      => open,
        stat_tx_unicast            => open,
        stat_tx_vlan               => open,

        ctl_tx_enable       => (not cmac_rx_remote_fault),
        ctl_tx_send_idle    => '0',
        ctl_tx_send_rfi     => cmac_rx_local_fault_int,
        ctl_tx_send_lfi     => '0',
        ctl_tx_test_pattern => '0',

        core_tx_reset => cmac_reset,

        tx_ovfout  => open,
        tx_rdyout  => cmac_tx_lbus_rdy,
        tx_unfout  => open,
        tx_datain0 => cmac_tx_lbus_data(0),
        tx_datain1 => cmac_tx_lbus_data(1),
        tx_datain2 => cmac_tx_lbus_data(2),
        tx_datain3 => cmac_tx_lbus_data(3),
        tx_enain0  => cmac_tx_lbus_ena(0),
        tx_enain1  => cmac_tx_lbus_ena(1),
        tx_enain2  => cmac_tx_lbus_ena(2),
        tx_enain3  => cmac_tx_lbus_ena(3),
        tx_eopin0  => cmac_tx_lbus_eop(0),
        tx_eopin1  => cmac_tx_lbus_eop(1),
        tx_eopin2  => cmac_tx_lbus_eop(2),
        tx_eopin3  => cmac_tx_lbus_eop(3),
        tx_errin0  => cmac_tx_lbus_err(0),
        tx_errin1  => cmac_tx_lbus_err(1),
        tx_errin2  => cmac_tx_lbus_err(2),
        tx_errin3  => cmac_tx_lbus_err(3),
        tx_mtyin0  => cmac_tx_lbus_mty(0),
        tx_mtyin1  => cmac_tx_lbus_mty(1),
        tx_mtyin2  => cmac_tx_lbus_mty(2),
        tx_mtyin3  => cmac_tx_lbus_mty(3),
        tx_sopin0  => cmac_tx_lbus_sop(0),
        tx_sopin1  => cmac_tx_lbus_sop(1),
        tx_sopin2  => cmac_tx_lbus_sop(2),
        tx_sopin3  => cmac_tx_lbus_sop(3),
        tx_preamblein => X"55555555555555",
        --
        ctl_tx_rsfec_enable             => cmac_fec_tx_en,
        ctl_rx_rsfec_enable             => cmac_fec_rx_en,
        ctl_rsfec_ieee_error_indication_mode => '0',
        ctl_rx_rsfec_enable_correction  => cmac_fec_cor_en,
        ctl_rx_rsfec_enable_indication  => cmac_fec_ind_en,
        stat_rx_rsfec_am_lock0          => cmac_fec_am_lock(0),
        stat_rx_rsfec_am_lock1          => cmac_fec_am_lock(1),
        stat_rx_rsfec_am_lock2          => cmac_fec_am_lock(2),
        stat_rx_rsfec_am_lock3          => cmac_fec_am_lock(3),
        stat_rx_rsfec_corrected_cw_inc  => cmac_fec_cor_inc,
        stat_rx_rsfec_uncorrected_cw_inc=> cmac_fec_uncor_inc,
        stat_rx_rsfec_cw_inc            => open,
        stat_rx_rsfec_err_count0_inc    => cmac_fec_err_inc(0),
        stat_rx_rsfec_err_count1_inc    => cmac_fec_err_inc(1),
        stat_rx_rsfec_err_count2_inc    => cmac_fec_err_inc(2),
        stat_rx_rsfec_err_count3_inc    => cmac_fec_err_inc(3),
        stat_rx_rsfec_hi_ser            => cmac_fec_hi_ser,
        stat_rx_rsfec_lane_alignment_status => cmac_fec_algn_stat,
        stat_rx_rsfec_lane_fill_0       => open,
        stat_rx_rsfec_lane_fill_1       => open,
        stat_rx_rsfec_lane_fill_2       => open,
        stat_rx_rsfec_lane_fill_3       => open,
        stat_rx_rsfec_lane_mapping      => cmac_fec_lane_map,
        --
        usr_tx_reset   => open,
        core_drp_reset => '0',
        drp_clk        => MI_CLK_PHY,
        drp_addr       => cmac_drpaddr(4)(9 downto 0),
        drp_di         => cmac_drpdi(4),
        drp_en         => cmac_drpen(4),
        drp_do         => cmac_drpdo(4),
        drp_rdy        => cmac_drprdy(4),
        drp_we         => cmac_drpwe(4)
    );

    -- =========================================================================
    --  ADAPTERS
    -- =========================================================================

    mfb2lbus_i : entity work.TX_MAC_LITE_ADAPTER_LBUS
    generic map(
        DEVICE => DEVICE
    )
    port map(
        CLK            => cmac_clk_322m,
        RESET          => cmac_rst_322m,

        IN_MFB_DATA    => RX_MFB_DATA(0),
        IN_MFB_SOF_POS => RX_MFB_SOF_POS(0),
        IN_MFB_EOF_POS => RX_MFB_EOF_POS(0),
        IN_MFB_SOF     => RX_MFB_SOF(0),
        IN_MFB_EOF     => RX_MFB_EOF(0),
        IN_MFB_SRC_RDY => RX_MFB_SRC_RDY(0),
        IN_MFB_DST_RDY => RX_MFB_DST_RDY(0),

        OUT_LBUS_DATA  => cmac_tx_lbus_data,
        OUT_LBUS_MTY   => cmac_tx_lbus_mty,
        OUT_LBUS_ENA   => cmac_tx_lbus_ena,
        OUT_LBUS_SOP   => cmac_tx_lbus_sop,
        OUT_LBUS_EOP   => cmac_tx_lbus_eop,
        OUT_LBUS_ERR   => cmac_tx_lbus_err,
        OUT_LBUS_RDY   => cmac_tx_lbus_rdy
    );

    lbus2mfb_i : entity work.RX_MAC_LITE_ADAPTER_LBUS
    generic map(
        DEVICE => DEVICE
    )
    port map(
        CLK             => cmac_clk_322m,
        RESET           => cmac_rst_322m,

        IN_LBUS_DATA    => cmac_rx_lbus_data,
        IN_LBUS_MTY     => cmac_rx_lbus_mty,
        IN_LBUS_ENA     => cmac_rx_lbus_ena,
        IN_LBUS_SOP     => cmac_rx_lbus_sop,
        IN_LBUS_EOP     => cmac_rx_lbus_eop,
        IN_LBUS_ERR     => cmac_rx_lbus_err,

        OUT_MFB_DATA    => TX_MFB_DATA(0),
        OUT_MFB_SOF_POS => TX_MFB_SOF_POS(0),
        OUT_MFB_EOF_POS => TX_MFB_EOF_POS(0),
        OUT_MFB_SOF     => TX_MFB_SOF(0),
        OUT_MFB_EOF     => TX_MFB_EOF(0),
        OUT_MFB_ERROR   => TX_MFB_ERROR(0),
        OUT_MFB_SRC_RDY => TX_MFB_SRC_RDY(0)
    );

end architecture;
