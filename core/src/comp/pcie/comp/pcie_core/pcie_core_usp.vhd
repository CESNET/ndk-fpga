-- pcie_core_usp.vhd: PCIe module for USP devices
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.combo_user_const.all;

use work.math_pack.all;
use work.type_pack.all;

Library UNISIM;
use UNISIM.vcomponents.all;

-- ============================================================================
--                                Description
-- ============================================================================

-- This is the specific wrapper around the Xilinx UlstraScale PCIe IP core.
-- It contains a number of debug components.
-- Streaming Debug Probes monitor SRC and DST RDY signals and and Event Counters monitor the number of available PCIe credits for each Hard IP core.
-- They are controlled over the MI interface.
--
-- **MI address space**
--
-- +----------------+----------------+------------------------------------------------------------------------------------------------+
-- | Hard IP | Component                                                                                            | Address range   |
-- +=========+======================================================================================================+=================+
-- |         | Streaming Debug (Master with one Probe)                                                              |   0x00 - 0x3F   |
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
-- |         | Streaming Debug (Master with one Probe)                                                              |   0x140 - 0x17F |
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
architecture USP of PCIE_CORE is

    constant VSEC_BASE_ADDRESS : natural := tsel(ENDPOINT_TYPE = "USP_PCIE4C", 16#E80#, 16#480#);
    constant XVC_BASE_ADDRESS  : natural := tsel(ENDPOINT_TYPE = "USP_PCIE4C", 16#EA0#, 16#4A0#);
    constant DTB_NEXT_POINTER  : natural := tsel(XVC_ENABLE, XVC_BASE_ADDRESS, 0);

    constant PCIE_HIPS         : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1 or ENDPOINT_MODE = 2),PCIE_ENDPOINTS,PCIE_ENDPOINTS/2);
    constant PCIE_IP_LANES     : natural := tsel(ENDPOINT_MODE = 1, PCIE_LANES/2, PCIE_LANES);
    constant AXI_DATA_WIDTH    : natural := CQ_MFB_REGIONS*256;
    constant AXI_CQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 183, 88);
    constant AXI_CCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 81, 33);
    constant AXI_RQUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 137, 62);
    constant AXI_RCUSER_WIDTH  : natural := tsel((ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1), 161, 75);

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
    constant DBG_PROBES              : natural := 1;
    -- Address offset for each Streaming Debug Probe.
    constant DBG_PROBE_OFFSET        : natural := 16#40#;
    -- Address offset of all Debug Probes per Endpoint.
    constant DBG_PROBES_OFFSET       : natural := DBG_PROBES*DBG_PROBE_OFFSET;
    -- Array of names (4-letter IDs) of Streaming Debug Probes
    -- This constant contains just the names of Probes of a single Streaming Debug Master.
    constant DBG_PROBE_STR           : string := "PRQ0"; -- PCIe RQ stream 0
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

    component pcie4_uscale_plus
    port (
        user_clk                               :  out  std_logic;
        user_reset                             :  out  std_logic;
        user_lnk_up                            :  out  std_logic;

        pci_exp_rxp                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_rxn                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_txp                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_txn                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);

        s_axis_rq_tdata                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        s_axis_rq_tkeep                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        s_axis_rq_tlast                        :  in   std_logic;
        s_axis_rq_tready                       :  out  std_logic_vector(3     downto  0);
        s_axis_rq_tuser                        :  in   std_logic_vector(AXI_RQUSER_WIDTH-1  downto 0);
        s_axis_rq_tvalid                       :  in   std_logic;
        m_axis_rc_tdata                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        m_axis_rc_tkeep                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        m_axis_rc_tlast                        :  out  std_logic;
        m_axis_rc_tready                       :  in   std_logic;
        m_axis_rc_tuser                        :  out  std_logic_vector(AXI_RCUSER_WIDTH-1  downto 0);
        m_axis_rc_tvalid                       :  out  std_logic;
        m_axis_cq_tdata                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        m_axis_cq_tkeep                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        m_axis_cq_tlast                        :  out  std_logic;
        m_axis_cq_tready                       :  in   std_logic;
        m_axis_cq_tuser                        :  out  std_logic_vector(AXI_CQUSER_WIDTH-1  downto 0);
        m_axis_cq_tvalid                       :  out  std_logic;
        s_axis_cc_tdata                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        s_axis_cc_tkeep                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        s_axis_cc_tlast                        :  in   std_logic;
        s_axis_cc_tready                       :  out  std_logic_vector(3     downto  0);
        s_axis_cc_tuser                        :  in   std_logic_vector(AXI_CCUSER_WIDTH-1  downto 0);
        s_axis_cc_tvalid                       :  in   std_logic;
        pcie_rq_seq_num0                       :  out  std_logic_vector(5     downto  0);
        pcie_rq_seq_num_vld0                   :  out  std_logic;
        pcie_rq_seq_num1                       :  out  std_logic_vector(5     downto  0);
        pcie_rq_seq_num_vld1                   :  out  std_logic;
        pcie_rq_tag0                           :  out  std_logic_vector(7     downto  0);
        pcie_rq_tag1                           :  out  std_logic_vector(7     downto  0);
        pcie_rq_tag_av                         :  out  std_logic_vector(3     downto  0);
        pcie_rq_tag_vld0                       :  out  std_logic;
        pcie_rq_tag_vld1                       :  out  std_logic;
        pcie_tfc_nph_av                        :  out  std_logic_vector(3     downto  0);
        pcie_tfc_npd_av                        :  out  std_logic_vector(3     downto  0);
        pcie_cq_np_req                         :  in   std_logic_vector(1     downto  0);
        pcie_cq_np_req_count                   :  out  std_logic_vector(5     downto  0);
        cfg_phy_link_down                      :  out  std_logic;
        cfg_phy_link_status                    :  out  std_logic_vector(1     downto  0);
        cfg_negotiated_width                   :  out  std_logic_vector(2     downto  0);
        cfg_current_speed                      :  out  std_logic_vector(1     downto  0);
        cfg_max_payload                        :  out  std_logic_vector(1     downto  0);
        cfg_max_read_req                       :  out  std_logic_vector(2     downto  0);
        cfg_function_status                    :  out  std_logic_vector(15    downto  0);
        cfg_function_power_state               :  out  std_logic_vector(11    downto  0);
        cfg_vf_status                          :  out  std_logic_vector(503   downto  0);
        cfg_vf_power_state                     :  out  std_logic_vector(755   downto  0);
        cfg_link_power_state                   :  out  std_logic_vector(1     downto  0);
        cfg_mgmt_addr                          :  in   std_logic_vector(9     downto  0);
        cfg_mgmt_function_number               :  in   std_logic_vector(7     downto  0);
        cfg_mgmt_write                         :  in   std_logic;
        cfg_mgmt_write_data                    :  in   std_logic_vector(31    downto  0);
        cfg_mgmt_byte_enable                   :  in   std_logic_vector(3     downto  0);
        cfg_mgmt_read                          :  in   std_logic;
        cfg_mgmt_read_data                     :  out  std_logic_vector(31    downto  0);
        cfg_mgmt_read_write_done               :  out  std_logic;
        cfg_mgmt_debug_access                  :  in   std_logic;
        cfg_err_cor_out                        :  out  std_logic;
        cfg_err_nonfatal_out                   :  out  std_logic;
        cfg_err_fatal_out                      :  out  std_logic;
        cfg_local_error_valid                  :  out  std_logic;
        cfg_local_error_out                    :  out  std_logic_vector(4     downto  0);
        cfg_ltssm_state                        :  out  std_logic_vector(5     downto  0);
        cfg_rx_pm_state                        :  out  std_logic_vector(1     downto  0);
        cfg_tx_pm_state                        :  out  std_logic_vector(1     downto  0);
        cfg_rcb_status                         :  out  std_logic_vector(3     downto  0);
        cfg_obff_enable                        :  out  std_logic_vector(1     downto  0);
        cfg_pl_status_change                   :  out  std_logic;
        cfg_tph_requester_enable               :  out  std_logic_vector(3     downto  0);
        cfg_tph_st_mode                        :  out  std_logic_vector(11    downto  0);
        cfg_vf_tph_requester_enable            :  out  std_logic_vector(251   downto  0);
        cfg_vf_tph_st_mode                     :  out  std_logic_vector(755   downto  0);
        cfg_dsn                                :  in   std_logic_vector(63    downto  0);
        cfg_bus_number                         :  out  std_logic_vector(7     downto  0);
        cfg_msg_received                       :  out  std_logic;
        cfg_msg_received_data                  :  out  std_logic_vector(7    downto  0);
        cfg_msg_received_type                  :  out  std_logic_vector(4    downto  0);
        cfg_msg_transmit                       :  in   std_logic;
        cfg_msg_transmit_type                  :  in   std_logic_vector(2    downto  0);
        cfg_msg_transmit_data                  :  in   std_logic_vector(31   downto  0);
        cfg_msg_transmit_done                  :  out  std_logic;
        cfg_fc_ph                              :  out  std_logic_vector(7    downto  0);
        cfg_fc_pd                              :  out  std_logic_vector(11   downto  0);
        cfg_fc_nph                             :  out  std_logic_vector(7    downto  0);
        cfg_fc_npd                             :  out  std_logic_vector(11   downto  0);
        cfg_fc_cplh                            :  out  std_logic_vector(7    downto  0);
        cfg_fc_cpld                            :  out  std_logic_vector(11   downto  0);
        cfg_fc_sel                             :  in   std_logic_vector(2    downto  0);
        cfg_power_state_change_ack             :  in   std_logic;
        cfg_power_state_change_interrupt       :  out  std_logic;
        cfg_err_cor_in                         :  in   std_logic;
        cfg_err_uncor_in                       :  in   std_logic;
        cfg_flr_in_process                     :  out  std_logic_vector(3     downto  0);
        cfg_flr_done                           :  in   std_logic_vector(3     downto  0);
        cfg_vf_flr_in_process                  :  out  std_logic_vector(251   downto  0);
        cfg_vf_flr_func_num                    :  in   std_logic_vector(7     downto  0);
        cfg_vf_flr_done                        :  in   std_logic_vector(0     downto  0);
        cfg_link_training_enable               :  in   std_logic;
        cfg_ext_read_received                  :  out  std_logic;
        cfg_ext_write_received                 :  out  std_logic;
        cfg_ext_register_number                :  out  std_logic_vector(9     downto  0);
        cfg_ext_function_number                :  out  std_logic_vector(7     downto  0);
        cfg_ext_write_data                     :  out  std_logic_vector(31    downto  0);
        cfg_ext_write_byte_enable              :  out  std_logic_vector(3     downto  0);
        cfg_ext_read_data                      :  in   std_logic_vector(31    downto  0);
        cfg_ext_read_data_valid                :  in   std_logic;
        cfg_interrupt_int                      :  in   std_logic_vector(3    downto  0);
        cfg_interrupt_pending                  :  in   std_logic_vector(3    downto  0);
        cfg_interrupt_sent                     :  out  std_logic;
        cfg_interrupt_msi_sent                 :  out  std_logic;
        cfg_interrupt_msi_fail                 :  out  std_logic;
        cfg_interrupt_msi_function_number      :  in   std_logic_vector(7    downto  0);
        cfg_interrupt_msix_enable              :  out  std_logic_vector(3    downto  0);
        cfg_interrupt_msix_mask                :  out  std_logic_vector(3    downto  0);
        cfg_interrupt_msix_vf_enable           :  out  std_logic_vector(251  downto  0);
        cfg_interrupt_msix_vf_mask             :  out  std_logic_vector(251  downto  0);
        cfg_interrupt_msix_data                :  in   std_logic_vector(31   downto  0);
        cfg_interrupt_msix_address             :  in   std_logic_vector(63   downto  0);
        cfg_interrupt_msix_int                 :  in   std_logic;
        cfg_interrupt_msix_vec_pending         :  in   std_logic_vector(1    downto  0);
        cfg_interrupt_msix_vec_pending_status  :  out  std_logic_vector(0    downto  0);
        cfg_pm_aspm_l1_entry_reject            :  in   std_logic;
        cfg_pm_aspm_tx_l0s_entry_disable       :  in   std_logic;
        cfg_hot_reset_out                      :  out  std_logic;
        cfg_config_space_enable                :  in   std_logic;
        cfg_req_pm_transition_l23_ready        :  in   std_logic;
        cfg_hot_reset_in                       :  in   std_logic;
        cfg_ds_port_number                     :  in   std_logic_vector(7     downto  0);
        cfg_ds_bus_number                      :  in   std_logic_vector(7     downto  0);
        cfg_ds_device_number                   :  in   std_logic_vector(4     downto  0);
        sys_clk                                :  in   std_logic;
        sys_clk_gt                             :  in   std_logic;
        sys_reset                              :  in   std_logic;
        phy_rdy_out                            :  out  std_logic
    );
    end component;

    component pcie4_uscale_plus_1
    port (
        user_clk                               :  out  std_logic;
        user_reset                             :  out  std_logic;
        user_lnk_up                            :  out  std_logic;

        pci_exp_rxp                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_rxn                            :  in   std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_txp                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);
        pci_exp_txn                            :  out  std_logic_vector(PCIE_IP_LANES-1 downto 0);

        s_axis_rq_tdata                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        s_axis_rq_tkeep                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        s_axis_rq_tlast                        :  in   std_logic;
        s_axis_rq_tready                       :  out  std_logic_vector(3     downto  0);
        s_axis_rq_tuser                        :  in   std_logic_vector(AXI_RQUSER_WIDTH-1  downto 0);
        s_axis_rq_tvalid                       :  in   std_logic;
        m_axis_rc_tdata                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        m_axis_rc_tkeep                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        m_axis_rc_tlast                        :  out  std_logic;
        m_axis_rc_tready                       :  in   std_logic;
        m_axis_rc_tuser                        :  out  std_logic_vector(AXI_RCUSER_WIDTH-1  downto 0);
        m_axis_rc_tvalid                       :  out  std_logic;
        m_axis_cq_tdata                        :  out  std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        m_axis_cq_tkeep                        :  out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        m_axis_cq_tlast                        :  out  std_logic;
        m_axis_cq_tready                       :  in   std_logic;
        m_axis_cq_tuser                        :  out  std_logic_vector(AXI_CQUSER_WIDTH-1  downto 0);
        m_axis_cq_tvalid                       :  out  std_logic;
        s_axis_cc_tdata                        :  in   std_logic_vector(AXI_DATA_WIDTH-1    downto 0);
        s_axis_cc_tkeep                        :  in   std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        s_axis_cc_tlast                        :  in   std_logic;
        s_axis_cc_tready                       :  out  std_logic_vector(3     downto  0);
        s_axis_cc_tuser                        :  in   std_logic_vector(AXI_CCUSER_WIDTH-1  downto 0);
        s_axis_cc_tvalid                       :  in   std_logic;
        pcie_rq_seq_num0                       :  out  std_logic_vector(5     downto  0);
        pcie_rq_seq_num_vld0                   :  out  std_logic;
        pcie_rq_seq_num1                       :  out  std_logic_vector(5     downto  0);
        pcie_rq_seq_num_vld1                   :  out  std_logic;
        pcie_rq_tag0                           :  out  std_logic_vector(7     downto  0);
        pcie_rq_tag1                           :  out  std_logic_vector(7     downto  0);
        pcie_rq_tag_av                         :  out  std_logic_vector(3     downto  0);
        pcie_rq_tag_vld0                       :  out  std_logic;
        pcie_rq_tag_vld1                       :  out  std_logic;
        pcie_tfc_nph_av                        :  out  std_logic_vector(3     downto  0);
        pcie_tfc_npd_av                        :  out  std_logic_vector(3     downto  0);
        pcie_cq_np_req                         :  in   std_logic_vector(1     downto  0);
        pcie_cq_np_req_count                   :  out  std_logic_vector(5     downto  0);
        cfg_phy_link_down                      :  out  std_logic;
        cfg_phy_link_status                    :  out  std_logic_vector(1     downto  0);
        cfg_negotiated_width                   :  out  std_logic_vector(2     downto  0);
        cfg_current_speed                      :  out  std_logic_vector(1     downto  0);
        cfg_max_payload                        :  out  std_logic_vector(1     downto  0);
        cfg_max_read_req                       :  out  std_logic_vector(2     downto  0);
        cfg_function_status                    :  out  std_logic_vector(15    downto  0);
        cfg_function_power_state               :  out  std_logic_vector(11    downto  0);
        cfg_vf_status                          :  out  std_logic_vector(503   downto  0);
        cfg_vf_power_state                     :  out  std_logic_vector(755   downto  0);
        cfg_link_power_state                   :  out  std_logic_vector(1     downto  0);
        cfg_mgmt_addr                          :  in   std_logic_vector(9     downto  0);
        cfg_mgmt_function_number               :  in   std_logic_vector(7     downto  0);
        cfg_mgmt_write                         :  in   std_logic;
        cfg_mgmt_write_data                    :  in   std_logic_vector(31    downto  0);
        cfg_mgmt_byte_enable                   :  in   std_logic_vector(3     downto  0);
        cfg_mgmt_read                          :  in   std_logic;
        cfg_mgmt_read_data                     :  out  std_logic_vector(31    downto  0);
        cfg_mgmt_read_write_done               :  out  std_logic;
        cfg_mgmt_debug_access                  :  in   std_logic;
        cfg_err_cor_out                        :  out  std_logic;
        cfg_err_nonfatal_out                   :  out  std_logic;
        cfg_err_fatal_out                      :  out  std_logic;
        cfg_local_error_valid                  :  out  std_logic;
        cfg_local_error_out                    :  out  std_logic_vector(4     downto  0);
        cfg_ltssm_state                        :  out  std_logic_vector(5     downto  0);
        cfg_rx_pm_state                        :  out  std_logic_vector(1     downto  0);
        cfg_tx_pm_state                        :  out  std_logic_vector(1     downto  0);
        cfg_rcb_status                         :  out  std_logic_vector(3     downto  0);
        cfg_obff_enable                        :  out  std_logic_vector(1     downto  0);
        cfg_pl_status_change                   :  out  std_logic;
        cfg_tph_requester_enable               :  out  std_logic_vector(3     downto  0);
        cfg_tph_st_mode                        :  out  std_logic_vector(11    downto  0);
        cfg_vf_tph_requester_enable            :  out  std_logic_vector(251   downto  0);
        cfg_vf_tph_st_mode                     :  out  std_logic_vector(755   downto  0);
        cfg_dsn                                :  in   std_logic_vector(63    downto  0);
        cfg_bus_number                         :  out  std_logic_vector(7     downto  0);
        cfg_msg_received                       :  out  std_logic;
        cfg_msg_received_data                  :  out  std_logic_vector(7    downto  0);
        cfg_msg_received_type                  :  out  std_logic_vector(4    downto  0);
        cfg_msg_transmit                       :  in   std_logic;
        cfg_msg_transmit_type                  :  in   std_logic_vector(2    downto  0);
        cfg_msg_transmit_data                  :  in   std_logic_vector(31   downto  0);
        cfg_msg_transmit_done                  :  out  std_logic;
        cfg_fc_ph                              :  out  std_logic_vector(7    downto  0);
        cfg_fc_pd                              :  out  std_logic_vector(11   downto  0);
        cfg_fc_nph                             :  out  std_logic_vector(7    downto  0);
        cfg_fc_npd                             :  out  std_logic_vector(11   downto  0);
        cfg_fc_cplh                            :  out  std_logic_vector(7    downto  0);
        cfg_fc_cpld                            :  out  std_logic_vector(11   downto  0);
        cfg_fc_sel                             :  in   std_logic_vector(2    downto  0);
        cfg_power_state_change_ack             :  in   std_logic;
        cfg_power_state_change_interrupt       :  out  std_logic;
        cfg_err_cor_in                         :  in   std_logic;
        cfg_err_uncor_in                       :  in   std_logic;
        cfg_flr_in_process                     :  out  std_logic_vector(3     downto  0);
        cfg_flr_done                           :  in   std_logic_vector(3     downto  0);
        cfg_vf_flr_in_process                  :  out  std_logic_vector(251   downto  0);
        cfg_vf_flr_func_num                    :  in   std_logic_vector(7     downto  0);
        cfg_vf_flr_done                        :  in   std_logic_vector(0     downto  0);
        cfg_link_training_enable               :  in   std_logic;
        cfg_ext_read_received                  :  out  std_logic;
        cfg_ext_write_received                 :  out  std_logic;
        cfg_ext_register_number                :  out  std_logic_vector(9     downto  0);
        cfg_ext_function_number                :  out  std_logic_vector(7     downto  0);
        cfg_ext_write_data                     :  out  std_logic_vector(31    downto  0);
        cfg_ext_write_byte_enable              :  out  std_logic_vector(3     downto  0);
        cfg_ext_read_data                      :  in   std_logic_vector(31    downto  0);
        cfg_ext_read_data_valid                :  in   std_logic;
        cfg_interrupt_int                      :  in   std_logic_vector(3    downto  0);
        cfg_interrupt_pending                  :  in   std_logic_vector(3    downto  0);
        cfg_interrupt_sent                     :  out  std_logic;
        cfg_interrupt_msi_sent                 :  out  std_logic;
        cfg_interrupt_msi_fail                 :  out  std_logic;
        cfg_interrupt_msi_function_number      :  in   std_logic_vector(7    downto  0);
        cfg_interrupt_msix_enable              :  out  std_logic_vector(3    downto  0);
        cfg_interrupt_msix_mask                :  out  std_logic_vector(3    downto  0);
        cfg_interrupt_msix_vf_enable           :  out  std_logic_vector(251  downto  0);
        cfg_interrupt_msix_vf_mask             :  out  std_logic_vector(251  downto  0);
        cfg_interrupt_msix_data                :  in   std_logic_vector(31   downto  0);
        cfg_interrupt_msix_address             :  in   std_logic_vector(63   downto  0);
        cfg_interrupt_msix_int                 :  in   std_logic;
        cfg_interrupt_msix_vec_pending         :  in   std_logic_vector(1    downto  0);
        cfg_interrupt_msix_vec_pending_status  :  out  std_logic_vector(0    downto  0);
        cfg_pm_aspm_l1_entry_reject            :  in   std_logic;
        cfg_pm_aspm_tx_l0s_entry_disable       :  in   std_logic;
        cfg_hot_reset_out                      :  out  std_logic;
        cfg_config_space_enable                :  in   std_logic;
        cfg_req_pm_transition_l23_ready        :  in   std_logic;
        cfg_hot_reset_in                       :  in   std_logic;
        cfg_ds_port_number                     :  in   std_logic_vector(7     downto  0);
        cfg_ds_bus_number                      :  in   std_logic_vector(7     downto  0);
        cfg_ds_device_number                   :  in   std_logic_vector(4     downto  0);
        sys_clk                                :  in   std_logic;
        sys_clk_gt                             :  in   std_logic;
        sys_reset                              :  in   std_logic;
        phy_rdy_out                            :  out  std_logic
    );
    end component;

    component xvc_vsec
    port (
            clk                                : in    std_logic;
            pcie3_cfg_ext_function_number      : in    std_logic_vector(7 downto 0);
            pcie3_cfg_ext_read_data            : out   std_logic_vector(31 downto 0);
            pcie3_cfg_ext_read_data_valid      : out   std_logic;
            pcie3_cfg_ext_read_received        : in    std_logic;
            pcie3_cfg_ext_register_number      : in    std_logic_vector(9 downto 0);
            pcie3_cfg_ext_write_byte_enable    : in    std_logic_vector(3 downto 0);
            pcie3_cfg_ext_write_data           : in    std_logic_vector(31 downto 0);
            pcie3_cfg_ext_write_received       : in    std_logic
    );
    end component;

    signal pcie_sysclk_buf          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_sysclk_gt_buf       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_hip_clk             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_hip_rst             : std_logic_vector(PCIE_HIPS-1 downto 0);
    signal pcie_clk                 : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst_async           : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rst                 : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(RESET_WIDTH+1-1 downto 0);
    
    signal cfg_rcb_status           : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_max_payload          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal cfg_max_read_req         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(2 downto 0);
    signal cfg_phy_link_status      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(1 downto 0);
    signal user_lnk_up              : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal cfg_ext_read             : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_write            : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal cfg_ext_register         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(9 downto 0);
    signal cfg_ext_function         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(7 downto 0);
    signal cfg_ext_write_data       : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_write_be         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal cfg_ext_read_xvc_data    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_xvc_dv      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal cfg_ext_read_dtb_data    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dtb_dv      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0) := (others => '0');
    signal cfg_ext_read_data        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(31 downto 0);
    signal cfg_ext_read_dv          : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal pcie_cq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CQUSER_WIDTH-1 downto 0);
    signal pcie_cq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cq_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_cc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_CCUSER_WIDTH-1 downto 0);
    signal pcie_cc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_cc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_cc_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rq_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RQUSER_WIDTH-1 downto 0);
    signal pcie_rq_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rq_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rq_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_data         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH-1 downto 0);
    signal pcie_rc_axi_user         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_RCUSER_WIDTH-1 downto 0);
    signal pcie_rc_axi_last         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_keep         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(AXI_DATA_WIDTH/32-1 downto 0);
    signal pcie_rc_axi_valid        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal pcie_rc_axi_ready        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal s_axis_rq_tready         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);
    signal s_axis_cc_tready         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(3 downto 0);

    signal tag_assign_int       : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(16 -1 downto 0);
    signal tag_assign_vld_int   : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(2 -1 downto 0);

    --==============================================================================================
    -- Inserting Debug nets:
    --==============================================================================================
    signal cfg_phy_link_down        : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal pcie_phy_rdy_out         : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal cfg_negotiated_width     : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(2 downto 0);
    signal cfg_current_speed        : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_function_status      : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(15 downto 0);
    signal cfg_function_power_state : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(11 downto 0);
    signal cfg_link_power_state     : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_local_error_out      : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(4 downto 0);
    signal cfg_local_error_valid    : std_logic_vector(PCIE_ENDPOINTS -1 downto 0);
    signal cfg_rx_pm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_tx_pm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(1 downto 0);
    signal cfg_ltssm_state          : slv_array_t(PCIE_ENDPOINTS -1 downto 0)(5 downto 0);

    -- attribute mark_debug                 : string;
    -- special signals for debugging
    -- attribute mark_debug of pcie_cq_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_cq_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_cc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_cc_axi_valid : signal is "true";

    -- attribute mark_debug of pcie_rc_axi_data  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_user  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_keep  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_last  : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_ready : signal is "true";
    -- attribute mark_debug of pcie_rc_axi_valid : signal is "true";

    -- attribute mark_debug of cfg_phy_link_down        : signal is "true";
    -- attribute mark_debug of cfg_phy_link_status      : signal is "true";
    -- attribute mark_debug of pcie_phy_rdy_out         : signal is "true";
    -- attribute mark_debug of cfg_max_payload          : signal is "true";
    -- attribute mark_debug of cfg_max_read_req         : signal is "true";

    -- attribute mark_debug of cfg_negotiated_width     : signal is "true";
    -- attribute mark_debug of cfg_current_speed        : signal is "true";
    -- attribute mark_debug of cfg_function_status      : signal is "true";
    -- attribute mark_debug of cfg_function_power_state : signal is "true";
    -- attribute mark_debug of cfg_link_power_state     : signal is "true";
    -- attribute mark_debug of cfg_rx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_tx_pm_state          : signal is "true";
    -- attribute mark_debug of cfg_ltssm_state          : signal is "true";
    -- attribute mark_debug of cfg_local_error_out      : signal is "true";
    -- attribute mark_debug of cfg_local_error_valid    : signal is "true";

    --==============================================================================================
    -- Other debug signals
    --==============================================================================================
    signal mi_split_dwr       : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_addr      : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_be        : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_rd        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_wr        : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_ardy      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_split_drd       : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_drdy      : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_sync_dwr        : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_addr       : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_be         : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_sync_rd         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_wr         : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_ardy       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);
    signal mi_sync_drd        : slv_array_t     (PCIE_ENDPOINTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_sync_drdy       : std_logic_vector(PCIE_ENDPOINTS-1 downto 0);

    signal mi_split_dbg_dwr   : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_addr  : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_be    : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_dbg_rd    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_wr    : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_ardy  : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);
    signal mi_split_dbg_drd   : slv_array_2d_t(PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dbg_drdy  : slv_array_t   (PCIE_ENDPOINTS-1 downto 0)(1+DBG_EVENTS-1 downto 0);

    -- signal debug_block        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);
    -- signal debug_drop         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);
    -- signal debug_sop          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES*            RQ_MFB_REGIONS-1 downto 0);
    -- signal debug_eop          : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES*            RQ_MFB_REGIONS-1 downto 0);
    signal debug_src_rdy      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);
    signal debug_dst_rdy      : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_PROBES-1 downto 0);

    -- Watched signals:
    -- 4 signals, each with 4 ranges => 4 bits for each watched signal
    -- Any changes and addition of other signals must be also reflected in constants (DBG_EVENT_SIGNALS, DBG_EVENT_RANGES)
    signal eve_ph             : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd             : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph            : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd            : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);    

    signal eve_ph_reg         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_pd_reg         : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_nph_reg        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);
    signal eve_npd_reg        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(4-1 downto 0);

    signal eve_all_reg        : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(DBG_EVENTS-1 downto 0);

    signal dbg_credits_ph     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_pd     : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    signal dbg_credits_nph    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)( 7 downto 0);
    signal dbg_credits_npd    : slv_array_t(PCIE_ENDPOINTS-1 downto 0)(11 downto 0);
    --==============================================================================================

begin

    assert (ENDPOINT_MODE = 0 or ENDPOINT_MODE = 1 or ENDPOINT_MODE = 2)
        report "Xilinx USP PCIe Wrapper: Only values 0, 1 and 2 are supported for parameter ENDPOINT_MODE!"
        severity failure;

    assert (PCIE_ENDPOINTS=1 or PCIE_ENDPOINTS=2)
        report "Xilinx USP PCIe Wrapper: Only values 0 and 1 are supported for parameter PCIE_ENDPOINTS!"
        severity failure;

    assert DEVICE="ULTRASCALE"
        report "Xilinx USP PCIe Wrapper: Only ULTRASCALE+ device is supported!"
        severity failure;

    -- =========================================================================
    --  PCIE IP CORE
    -- =========================================================================

    pcie_mode_0_2_g : if (ENDPOINT_MODE=0 or ENDPOINT_MODE=2) generate

        pcie_hip_g : for i in 0 to PCIE_HIPS-1 generate
            pcie_ibuf_i : IBUFDS_GTE4
            generic map (
                REFCLK_HROW_CK_SEL => "00"
            )
            port map (
                I     => PCIE_SYSCLK_P(i*PCIE_CLKS),
                IB    => PCIE_SYSCLK_N(i*PCIE_CLKS),
                O     => pcie_sysclk_gt_buf(i),
                ODIV2 => pcie_sysclk_buf(i),
                CEB   => '0'
            );

            pcie_rq_axi_ready(i) <= s_axis_rq_tready(i)(0);
            pcie_cc_axi_ready(i) <= s_axis_cc_tready(i)(0);

            pcie_clk(i) <= pcie_hip_clk(i);

            TAG_ASSIGN(i)     <= tag_assign_int(i)(RQ_MFB_REGIONS*8 -1 downto 0);
            TAG_ASSIGN_VLD(i) <= tag_assign_vld_int(i)(RQ_MFB_REGIONS -1 downto 0);

            pcie0_g : if (i=0) generate
                pcie_i : pcie4_uscale_plus
                port map (
                    sys_clk                           => pcie_sysclk_buf(i),
                    sys_clk_gt                        => pcie_sysclk_gt_buf(i),
                    sys_reset                         => PCIE_SYSRST_N(i),

                    pci_exp_txn                       => PCIE_TX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_txp                       => PCIE_TX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxn                       => PCIE_RX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxp                       => PCIE_RX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),

                    user_clk                          => pcie_hip_clk(i),
                    user_reset                        => pcie_hip_rst(i),
                    user_lnk_up                       => user_lnk_up(i),

                    s_axis_rq_tlast                   => pcie_rq_axi_last(i),
                    s_axis_rq_tdata                   => pcie_rq_axi_data(i),
                    s_axis_rq_tuser                   => pcie_rq_axi_user(i),
                    s_axis_rq_tkeep                   => pcie_rq_axi_keep(i),
                    s_axis_rq_tready                  => s_axis_rq_tready(i),
                    s_axis_rq_tvalid                  => pcie_rq_axi_valid(i),
                    m_axis_rc_tdata                   => pcie_rc_axi_data(i),
                    m_axis_rc_tuser                   => pcie_rc_axi_user(i),
                    m_axis_rc_tlast                   => pcie_rc_axi_last(i),
                    m_axis_rc_tkeep                   => pcie_rc_axi_keep(i),
                    m_axis_rc_tvalid                  => pcie_rc_axi_valid(i),
                    m_axis_rc_tready                  => pcie_rc_axi_ready(i),
                    m_axis_cq_tdata                   => pcie_cq_axi_data(i),
                    m_axis_cq_tuser                   => pcie_cq_axi_user(i),
                    m_axis_cq_tlast                   => pcie_cq_axi_last(i),
                    m_axis_cq_tkeep                   => pcie_cq_axi_keep(i),
                    m_axis_cq_tvalid                  => pcie_cq_axi_valid(i),
                    m_axis_cq_tready                  => pcie_cq_axi_ready(i),
                    s_axis_cc_tdata                   => pcie_cc_axi_data(i),
                    s_axis_cc_tuser                   => pcie_cc_axi_user(i),
                    s_axis_cc_tlast                   => pcie_cc_axi_last(i),
                    s_axis_cc_tkeep                   => pcie_cc_axi_keep(i),
                    s_axis_cc_tvalid                  => pcie_cc_axi_valid(i),
                    s_axis_cc_tready                  => s_axis_cc_tready(i),

                    pcie_rq_seq_num0                  => open,
                    pcie_rq_seq_num_vld0              => open,
                    pcie_rq_tag0                      => tag_assign_int(i)(7 downto 0),
                    pcie_rq_tag_vld0                  => tag_assign_vld_int(i)(0),
                    pcie_rq_tag1                      => tag_assign_int(i)(15 downto 8),
                    pcie_rq_tag_vld1                  => tag_assign_vld_int(i)(1),

                    pcie_cq_np_req                    => (others => '1'),
                    pcie_cq_np_req_count              => open,

                    cfg_phy_link_down                 => cfg_phy_link_down(i),
                    cfg_phy_link_status               => cfg_phy_link_status(i),
                    cfg_negotiated_width              => cfg_negotiated_width(i),
                    cfg_current_speed                 => cfg_current_speed(i),
                    cfg_max_payload                   => cfg_max_payload(i),
                    cfg_max_read_req                  => cfg_max_read_req(i),
                    cfg_function_status               => cfg_function_status(i),
                    cfg_function_power_state          => cfg_function_power_state(i),
                    cfg_vf_status                     => open,
                    cfg_vf_power_state                => open,
                    cfg_link_power_state              => cfg_link_power_state(i),
                    cfg_mgmt_addr                     => (others => '0'),
                    cfg_mgmt_function_number          => (others => '0'),
                    cfg_mgmt_write                    => '0',
                    cfg_mgmt_write_data               => (others => '0'),
                    cfg_mgmt_byte_enable              => (others => '0'),
                    cfg_mgmt_read                     => '0',
                    cfg_mgmt_read_data                => open,
                    cfg_mgmt_read_write_done          => open,
                    cfg_mgmt_debug_access             => '0',
                    cfg_err_cor_out                   => open,
                    cfg_err_nonfatal_out              => open,
                    cfg_err_fatal_out                 => open,
                    cfg_local_error_valid             => cfg_local_error_valid(i),
                    cfg_local_error_out               => cfg_local_error_out(i),
                    cfg_ltssm_state                   => cfg_ltssm_state(i),
                    cfg_rx_pm_state                   => cfg_rx_pm_state(i),
                    cfg_tx_pm_state                   => cfg_tx_pm_state(i),
                    cfg_rcb_status                    => cfg_rcb_status(i),
                    cfg_obff_enable                   => open,
                    cfg_pl_status_change              => open,
                    cfg_tph_requester_enable          => open,
                    cfg_tph_st_mode                   => open,
                    cfg_vf_tph_requester_enable       => open,
                    cfg_vf_tph_st_mode                => open,
                    cfg_dsn                           => (others => '0'),
                    cfg_bus_number                    => open,
                    cfg_msg_received                  => open,
                    cfg_msg_received_data             => open,
                    cfg_msg_received_type             => open,
                    cfg_msg_transmit                  => '0',
                    cfg_msg_transmit_type             => (others => '0'),
                    cfg_msg_transmit_data             => (others => '0'),
                    cfg_msg_transmit_done             => open,
                    cfg_fc_ph                         => dbg_credits_ph (i),
                    cfg_fc_pd                         => dbg_credits_pd (i),
                    cfg_fc_nph                        => dbg_credits_nph(i),
                    cfg_fc_npd                        => dbg_credits_npd(i),
                    cfg_fc_cplh                       => open,
                    cfg_fc_cpld                       => open,
                    cfg_fc_sel                        => (others => '0'),
                    cfg_power_state_change_ack        => '0',
                    cfg_power_state_change_interrupt  => open,
                    cfg_err_cor_in                    => '0',
                    cfg_err_uncor_in                  => '0',
                    cfg_flr_in_process                => open,
                    cfg_flr_done                      => (others => '0'),
                    cfg_vf_flr_in_process             => open,
                    cfg_vf_flr_func_num               => (others => '0'),
                    cfg_vf_flr_done                   => (others => '0'),
                    cfg_link_training_enable          => '1',
                    cfg_ext_read_received             => cfg_ext_read(i),
                    cfg_ext_write_received            => cfg_ext_write(i),
                    cfg_ext_register_number           => cfg_ext_register(i),
                    cfg_ext_function_number           => cfg_ext_function(i),
                    cfg_ext_write_data                => cfg_ext_write_data(i),
                    cfg_ext_write_byte_enable         => cfg_ext_write_be(i),
                    cfg_ext_read_data                 => cfg_ext_read_data(i),
                    cfg_ext_read_data_valid           => cfg_ext_read_dv(i),
                    cfg_interrupt_int                 => (others => '0'),
                    cfg_interrupt_pending             => (others => '0'),
                    cfg_interrupt_sent                => open,
                    cfg_interrupt_msi_sent            => open,
                    cfg_interrupt_msi_fail            => open,
                    cfg_interrupt_msi_function_number => (others => '0'),
                    cfg_interrupt_msix_enable         => open,
                    cfg_interrupt_msix_mask           => open,
                    cfg_interrupt_msix_vf_enable      => open,
                    cfg_interrupt_msix_vf_mask        => open,
                    cfg_interrupt_msix_data           => (others => '0'),
                    cfg_interrupt_msix_address        => (others => '0'),
                    cfg_interrupt_msix_int            => '0',
                    cfg_interrupt_msix_vec_pending    => (others => '0'),
                    cfg_interrupt_msix_vec_pending_status => open,
                    cfg_pm_aspm_l1_entry_reject       => '0',
                    cfg_pm_aspm_tx_l0s_entry_disable  => '0',
                    cfg_hot_reset_out                 => open,
                    cfg_config_space_enable           => '1',
                    cfg_req_pm_transition_l23_ready   => '0',
                    cfg_hot_reset_in                  => '0',
                    cfg_ds_port_number                => (others => '0'),
                    cfg_ds_bus_number                 => (others => '0'),
                    cfg_ds_device_number              => (others => '0'),
                    phy_rdy_out                       => pcie_phy_rdy_out(i)
                );
            end generate;
            pcie1_g : if (i=1) generate
                pcie_i : pcie4_uscale_plus_1
                port map (
                    sys_clk                           => pcie_sysclk_buf(i),
                    sys_clk_gt                        => pcie_sysclk_gt_buf(i),
                    sys_reset                         => PCIE_SYSRST_N(i),

                    pci_exp_txn                       => PCIE_TX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_txp                       => PCIE_TX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxn                       => PCIE_RX_N((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),
                    pci_exp_rxp                       => PCIE_RX_P((i+1)*PCIE_IP_LANES-1 downto i*PCIE_IP_LANES),

                    user_clk                          => pcie_hip_clk(i),
                    user_reset                        => pcie_hip_rst(i),
                    user_lnk_up                       => user_lnk_up(i),

                    s_axis_rq_tlast                   => pcie_rq_axi_last(i),
                    s_axis_rq_tdata                   => pcie_rq_axi_data(i),
                    s_axis_rq_tuser                   => pcie_rq_axi_user(i),
                    s_axis_rq_tkeep                   => pcie_rq_axi_keep(i),
                    s_axis_rq_tready                  => s_axis_rq_tready(i),
                    s_axis_rq_tvalid                  => pcie_rq_axi_valid(i),
                    m_axis_rc_tdata                   => pcie_rc_axi_data(i),
                    m_axis_rc_tuser                   => pcie_rc_axi_user(i),
                    m_axis_rc_tlast                   => pcie_rc_axi_last(i),
                    m_axis_rc_tkeep                   => pcie_rc_axi_keep(i),
                    m_axis_rc_tvalid                  => pcie_rc_axi_valid(i),
                    m_axis_rc_tready                  => pcie_rc_axi_ready(i),
                    m_axis_cq_tdata                   => pcie_cq_axi_data(i),
                    m_axis_cq_tuser                   => pcie_cq_axi_user(i),
                    m_axis_cq_tlast                   => pcie_cq_axi_last(i),
                    m_axis_cq_tkeep                   => pcie_cq_axi_keep(i),
                    m_axis_cq_tvalid                  => pcie_cq_axi_valid(i),
                    m_axis_cq_tready                  => pcie_cq_axi_ready(i),
                    s_axis_cc_tdata                   => pcie_cc_axi_data(i),
                    s_axis_cc_tuser                   => pcie_cc_axi_user(i),
                    s_axis_cc_tlast                   => pcie_cc_axi_last(i),
                    s_axis_cc_tkeep                   => pcie_cc_axi_keep(i),
                    s_axis_cc_tvalid                  => pcie_cc_axi_valid(i),
                    s_axis_cc_tready                  => s_axis_cc_tready(i),

                    pcie_rq_seq_num0                  => open,
                    pcie_rq_seq_num_vld0              => open,
                    pcie_rq_tag0                      => tag_assign_int(i)(7 downto 0),
                    pcie_rq_tag_vld0                  => tag_assign_vld_int(i)(0),
                    pcie_rq_tag1                      => tag_assign_int(i)(15 downto 8),
                    pcie_rq_tag_vld1                  => tag_assign_vld_int(i)(1),

                    pcie_cq_np_req                    => (others => '1'),
                    pcie_cq_np_req_count              => open,

                    cfg_phy_link_down                 => cfg_phy_link_down(i),
                    cfg_phy_link_status               => cfg_phy_link_status(i),
                    cfg_negotiated_width              => cfg_negotiated_width(i),
                    cfg_current_speed                 => cfg_current_speed(i),
                    cfg_max_payload                   => cfg_max_payload(i),
                    cfg_max_read_req                  => cfg_max_read_req(i),
                    cfg_function_status               => cfg_function_status(i),
                    cfg_function_power_state          => cfg_function_power_state(i),
                    cfg_vf_status                     => open,
                    cfg_vf_power_state                => open,
                    cfg_link_power_state              => cfg_link_power_state(i),
                    cfg_mgmt_addr                     => (others => '0'),
                    cfg_mgmt_function_number          => (others => '0'),
                    cfg_mgmt_write                    => '0',
                    cfg_mgmt_write_data               => (others => '0'),
                    cfg_mgmt_byte_enable              => (others => '0'),
                    cfg_mgmt_read                     => '0',
                    cfg_mgmt_read_data                => open,
                    cfg_mgmt_read_write_done          => open,
                    cfg_mgmt_debug_access             => '0',
                    cfg_err_cor_out                   => open,
                    cfg_err_nonfatal_out              => open,
                    cfg_err_fatal_out                 => open,
                    cfg_local_error_valid             => cfg_local_error_valid(i),
                    cfg_local_error_out               => cfg_local_error_out(i),
                    cfg_ltssm_state                   => cfg_ltssm_state(i),
                    cfg_rx_pm_state                   => cfg_rx_pm_state(i),
                    cfg_tx_pm_state                   => cfg_tx_pm_state(i),
                    cfg_rcb_status                    => cfg_rcb_status(i),
                    cfg_obff_enable                   => open,
                    cfg_pl_status_change              => open,
                    cfg_tph_requester_enable          => open,
                    cfg_tph_st_mode                   => open,
                    cfg_vf_tph_requester_enable       => open,
                    cfg_vf_tph_st_mode                => open,
                    cfg_dsn                           => (others => '0'),
                    cfg_bus_number                    => open,
                    cfg_msg_received                  => open,
                    cfg_msg_received_data             => open,
                    cfg_msg_received_type             => open,
                    cfg_msg_transmit                  => '0',
                    cfg_msg_transmit_type             => (others => '0'),
                    cfg_msg_transmit_data             => (others => '0'),
                    cfg_msg_transmit_done             => open,
                    cfg_fc_ph                         => open,
                    cfg_fc_pd                         => open,
                    cfg_fc_nph                        => open,
                    cfg_fc_npd                        => open,
                    cfg_fc_cplh                       => open,
                    cfg_fc_cpld                       => open,
                    cfg_fc_sel                        => (others => '0'),
                    cfg_power_state_change_ack        => '0',
                    cfg_power_state_change_interrupt  => open,
                    cfg_err_cor_in                    => '0',
                    cfg_err_uncor_in                  => '0',
                    cfg_flr_in_process                => open,
                    cfg_flr_done                      => (others => '0'),
                    cfg_vf_flr_in_process             => open,
                    cfg_vf_flr_func_num               => (others => '0'),
                    cfg_vf_flr_done                   => (others => '0'),
                    cfg_link_training_enable          => '1',
                    cfg_ext_read_received             => cfg_ext_read(i),
                    cfg_ext_write_received            => cfg_ext_write(i),
                    cfg_ext_register_number           => cfg_ext_register(i),
                    cfg_ext_function_number           => cfg_ext_function(i),
                    cfg_ext_write_data                => cfg_ext_write_data(i),
                    cfg_ext_write_byte_enable         => cfg_ext_write_be(i),
                    cfg_ext_read_data                 => cfg_ext_read_data(i),
                    cfg_ext_read_data_valid           => cfg_ext_read_dv(i),
                    cfg_interrupt_int                 => (others => '0'),
                    cfg_interrupt_pending             => (others => '0'),
                    cfg_interrupt_sent                => open,
                    cfg_interrupt_msi_sent            => open,
                    cfg_interrupt_msi_fail            => open,
                    cfg_interrupt_msi_function_number => (others => '0'),
                    cfg_interrupt_msix_enable         => open,
                    cfg_interrupt_msix_mask           => open,
                    cfg_interrupt_msix_vf_enable      => open,
                    cfg_interrupt_msix_vf_mask        => open,
                    cfg_interrupt_msix_data           => (others => '0'),
                    cfg_interrupt_msix_address        => (others => '0'),
                    cfg_interrupt_msix_int            => '0',
                    cfg_interrupt_msix_vec_pending    => (others => '0'),
                    cfg_interrupt_msix_vec_pending_status => open,
                    cfg_pm_aspm_l1_entry_reject       => '0',
                    cfg_pm_aspm_tx_l0s_entry_disable  => '0',
                    cfg_hot_reset_out                 => open,
                    cfg_config_space_enable           => '1',
                    cfg_req_pm_transition_l23_ready   => '0',
                    cfg_hot_reset_in                  => '0',
                    cfg_ds_port_number                => (others => '0'),
                    cfg_ds_bus_number                 => (others => '0'),
                    cfg_ds_device_number              => (others => '0'),
                    phy_rdy_out                       => pcie_phy_rdy_out(i)
                );
            end generate;
        end generate;
    end generate;

    pcie_mode_1_g : if (ENDPOINT_MODE=1) generate

        pcie_hip_g : for i in 0 to PCIE_HIPS/2-1 generate

            pcie_i : for j in 0 to 1 generate

                pcie_ibuf_i_j : IBUFDS_GTE4
                generic map (
                    REFCLK_HROW_CK_SEL => "00"
                )
                port map (
                    I     => PCIE_SYSCLK_P(i*PCIE_CLKS+j),
                    IB    => PCIE_SYSCLK_N(i*PCIE_CLKS+j),
                    O     => pcie_sysclk_gt_buf(2*i+j),
                    ODIV2 => pcie_sysclk_buf(2*i+j),
                    CEB   => '0'
                );

                pcie_rq_axi_ready(2*i+j) <= s_axis_rq_tready(2*i+j)(0);
                pcie_cc_axi_ready(2*i+j) <= s_axis_cc_tready(2*i+j)(0);

                pcie_clk(2*i+j) <= pcie_hip_clk(2*i+j);

                TAG_ASSIGN(2*i+j)     <= tag_assign_int(2*i+j)(RQ_MFB_REGIONS*8 -1 downto 0);
                TAG_ASSIGN_VLD(2*i+j) <= tag_assign_vld_int(2*i+j)(RQ_MFB_REGIONS -1 downto 0);

                pcie0_i : if (j=0) generate
                    pcie4_uscale_plus_0_i : pcie4_uscale_plus
                    port map (
                        sys_clk                           => pcie_sysclk_buf(2*i+j),
                        sys_clk_gt                        => pcie_sysclk_gt_buf(2*i+j),
                        sys_reset                         => PCIE_SYSRST_N(i),

                        pci_exp_txn                       => PCIE_TX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_txp                       => PCIE_TX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxn                       => PCIE_RX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxp                       => PCIE_RX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),

                        user_clk                          => pcie_hip_clk(2*i+j),
                        user_reset                        => pcie_hip_rst(2*i+j),
                        user_lnk_up                       => user_lnk_up(2*i+j),

                        s_axis_rq_tlast                   => pcie_rq_axi_last(2*i+j),
                        s_axis_rq_tdata                   => pcie_rq_axi_data(2*i+j),
                        s_axis_rq_tuser                   => pcie_rq_axi_user(2*i+j),
                        s_axis_rq_tkeep                   => pcie_rq_axi_keep(2*i+j),
                        s_axis_rq_tready                  => s_axis_rq_tready(2*i+j),
                        s_axis_rq_tvalid                  => pcie_rq_axi_valid(2*i+j),
                        m_axis_rc_tdata                   => pcie_rc_axi_data(2*i+j),
                        m_axis_rc_tuser                   => pcie_rc_axi_user(2*i+j),
                        m_axis_rc_tlast                   => pcie_rc_axi_last(2*i+j),
                        m_axis_rc_tkeep                   => pcie_rc_axi_keep(2*i+j),
                        m_axis_rc_tvalid                  => pcie_rc_axi_valid(2*i+j),
                        m_axis_rc_tready                  => pcie_rc_axi_ready(2*i+j),
                        m_axis_cq_tdata                   => pcie_cq_axi_data(2*i+j),
                        m_axis_cq_tuser                   => pcie_cq_axi_user(2*i+j),
                        m_axis_cq_tlast                   => pcie_cq_axi_last(2*i+j),
                        m_axis_cq_tkeep                   => pcie_cq_axi_keep(2*i+j),
                        m_axis_cq_tvalid                  => pcie_cq_axi_valid(2*i+j),
                        m_axis_cq_tready                  => pcie_cq_axi_ready(2*i+j),
                        s_axis_cc_tdata                   => pcie_cc_axi_data(2*i+j),
                        s_axis_cc_tuser                   => pcie_cc_axi_user(2*i+j),
                        s_axis_cc_tlast                   => pcie_cc_axi_last(2*i+j),
                        s_axis_cc_tkeep                   => pcie_cc_axi_keep(2*i+j),
                        s_axis_cc_tvalid                  => pcie_cc_axi_valid(2*i+j),
                        s_axis_cc_tready                  => s_axis_cc_tready(2*i+j),

                        pcie_rq_seq_num0                  => open,
                        pcie_rq_seq_num_vld0              => open,
                        pcie_rq_tag0                      => tag_assign_int(2*i+j)(7 downto 0),
                        pcie_rq_tag_vld0                  => tag_assign_vld_int(2*i+j)(0),
                        pcie_rq_tag1                      => tag_assign_int(2*i+j)(15 downto 8),
                        pcie_rq_tag_vld1                  => tag_assign_vld_int(2*i+j)(1),

                        pcie_cq_np_req                    => (others => '1'),
                        pcie_cq_np_req_count              => open,

                        cfg_phy_link_down                 => cfg_phy_link_down(2*i+j),
                        cfg_phy_link_status               => cfg_phy_link_status(2*i+j),
                        cfg_negotiated_width              => cfg_negotiated_width(2*i+j),
                        cfg_current_speed                 => cfg_current_speed(2*i+j),
                        cfg_max_payload                   => cfg_max_payload(2*i+j),
                        cfg_max_read_req                  => cfg_max_read_req(2*i+j),
                        cfg_function_status               => cfg_function_status(2*i+j),
                        cfg_function_power_state          => cfg_function_power_state(2*i+j),
                        cfg_vf_status                     => open,
                        cfg_vf_power_state                => open,
                        cfg_link_power_state              => cfg_link_power_state(2*i+j),
                        cfg_mgmt_addr                     => (others => '0'),
                        cfg_mgmt_function_number          => (others => '0'),
                        cfg_mgmt_write                    => '0',
                        cfg_mgmt_write_data               => (others => '0'),
                        cfg_mgmt_byte_enable              => (others => '0'),
                        cfg_mgmt_read                     => '0',
                        cfg_mgmt_read_data                => open,
                        cfg_mgmt_read_write_done          => open,
                        cfg_mgmt_debug_access             => '0',
                        cfg_err_cor_out                   => open,
                        cfg_err_nonfatal_out              => open,
                        cfg_err_fatal_out                 => open,
                        cfg_local_error_valid             => cfg_local_error_valid(2*i+j),
                        cfg_local_error_out               => cfg_local_error_out(2*i+j),
                        cfg_ltssm_state                   => cfg_ltssm_state(2*i+j),
                        cfg_rx_pm_state                   => cfg_rx_pm_state(2*i+j),
                        cfg_tx_pm_state                   => cfg_tx_pm_state(2*i+j),
                        cfg_rcb_status                    => cfg_rcb_status(2*i+j),
                        cfg_obff_enable                   => open,
                        cfg_pl_status_change              => open,
                        cfg_tph_requester_enable          => open,
                        cfg_tph_st_mode                   => open,
                        cfg_vf_tph_requester_enable       => open,
                        cfg_vf_tph_st_mode                => open,
                        cfg_dsn                           => (others => '0'),
                        cfg_bus_number                    => open,
                        cfg_msg_received                  => open,
                        cfg_msg_received_data             => open,
                        cfg_msg_received_type             => open,
                        cfg_msg_transmit                  => '0',
                        cfg_msg_transmit_type             => (others => '0'),
                        cfg_msg_transmit_data             => (others => '0'),
                        cfg_msg_transmit_done             => open,
                        cfg_fc_ph                         => dbg_credits_ph (2*i+j),
                        cfg_fc_pd                         => dbg_credits_pd (2*i+j),
                        cfg_fc_nph                        => dbg_credits_nph(2*i+j),
                        cfg_fc_npd                        => dbg_credits_npd(2*i+j),
                        cfg_fc_cplh                       => open,
                        cfg_fc_cpld                       => open,
                        cfg_fc_sel                        => (others => '0'),
                        cfg_power_state_change_ack        => '0',
                        cfg_power_state_change_interrupt  => open,
                        cfg_err_cor_in                    => '0',
                        cfg_err_uncor_in                  => '0',
                        cfg_flr_in_process                => open,
                        cfg_flr_done                      => (others => '0'),
                        cfg_vf_flr_in_process             => open,
                        cfg_vf_flr_func_num               => (others => '0'),
                        cfg_vf_flr_done                   => (others => '0'),
                        cfg_link_training_enable          => '1',
                        cfg_ext_read_received             => cfg_ext_read(2*i+j),
                        cfg_ext_write_received            => cfg_ext_write(2*i+j),
                        cfg_ext_register_number           => cfg_ext_register(2*i+j),
                        cfg_ext_function_number           => cfg_ext_function(2*i+j),
                        cfg_ext_write_data                => cfg_ext_write_data(2*i+j),
                        cfg_ext_write_byte_enable         => cfg_ext_write_be(2*i+j),
                        cfg_ext_read_data                 => cfg_ext_read_data(2*i+j),
                        cfg_ext_read_data_valid           => cfg_ext_read_dv(2*i+j),
                        cfg_interrupt_int                 => (others => '0'),
                        cfg_interrupt_pending             => (others => '0'),
                        cfg_interrupt_sent                => open,
                        cfg_interrupt_msi_sent            => open,
                        cfg_interrupt_msi_fail            => open,
                        cfg_interrupt_msi_function_number => (others => '0'),
                        cfg_interrupt_msix_enable         => open,
                        cfg_interrupt_msix_mask           => open,
                        cfg_interrupt_msix_vf_enable      => open,
                        cfg_interrupt_msix_vf_mask        => open,
                        cfg_interrupt_msix_data           => (others => '0'),
                        cfg_interrupt_msix_address        => (others => '0'),
                        cfg_interrupt_msix_int            => '0',
                        cfg_interrupt_msix_vec_pending    => (others => '0'),
                        cfg_interrupt_msix_vec_pending_status => open,
                        cfg_pm_aspm_l1_entry_reject       => '0',
                        cfg_pm_aspm_tx_l0s_entry_disable  => '0',
                        cfg_hot_reset_out                 => open,
                        cfg_config_space_enable           => '1',
                        cfg_req_pm_transition_l23_ready   => '0',
                        cfg_hot_reset_in                  => '0',
                        cfg_ds_port_number                => (others => '0'),
                        cfg_ds_bus_number                 => (others => '0'),
                        cfg_ds_device_number              => (others => '0'),
                        phy_rdy_out                       => pcie_phy_rdy_out(2*i+j)
                    );
                end generate;
                pcie1_i : if (j=1) generate
                    pcie4_uscale_plus_1_i : pcie4_uscale_plus_1
                    port map (
                        sys_clk                           => pcie_sysclk_buf(2*i+j),
                        sys_clk_gt                        => pcie_sysclk_gt_buf(2*i+j),
                        sys_reset                         => PCIE_SYSRST_N(i),

                        pci_exp_txn                       => PCIE_TX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_txp                       => PCIE_TX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxn                       => PCIE_RX_N((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),
                        pci_exp_rxp                       => PCIE_RX_P((2*i+j+1)*PCIE_IP_LANES-1 downto (2*i+j)*PCIE_IP_LANES),

                        user_clk                          => pcie_hip_clk(2*i+j),
                        user_reset                        => pcie_hip_rst(2*i+j),
                        user_lnk_up                       => user_lnk_up(2*i+j),

                        s_axis_rq_tlast                   => pcie_rq_axi_last(2*i+j),
                        s_axis_rq_tdata                   => pcie_rq_axi_data(2*i+j),
                        s_axis_rq_tuser                   => pcie_rq_axi_user(2*i+j),
                        s_axis_rq_tkeep                   => pcie_rq_axi_keep(2*i+j),
                        s_axis_rq_tready                  => s_axis_rq_tready(2*i+j),
                        s_axis_rq_tvalid                  => pcie_rq_axi_valid(2*i+j),
                        m_axis_rc_tdata                   => pcie_rc_axi_data(2*i+j),
                        m_axis_rc_tuser                   => pcie_rc_axi_user(2*i+j),
                        m_axis_rc_tlast                   => pcie_rc_axi_last(2*i+j),
                        m_axis_rc_tkeep                   => pcie_rc_axi_keep(2*i+j),
                        m_axis_rc_tvalid                  => pcie_rc_axi_valid(2*i+j),
                        m_axis_rc_tready                  => pcie_rc_axi_ready(2*i+j),
                        m_axis_cq_tdata                   => pcie_cq_axi_data(2*i+j),
                        m_axis_cq_tuser                   => pcie_cq_axi_user(2*i+j),
                        m_axis_cq_tlast                   => pcie_cq_axi_last(2*i+j),
                        m_axis_cq_tkeep                   => pcie_cq_axi_keep(2*i+j),
                        m_axis_cq_tvalid                  => pcie_cq_axi_valid(2*i+j),
                        m_axis_cq_tready                  => pcie_cq_axi_ready(2*i+j),
                        s_axis_cc_tdata                   => pcie_cc_axi_data(2*i+j),
                        s_axis_cc_tuser                   => pcie_cc_axi_user(2*i+j),
                        s_axis_cc_tlast                   => pcie_cc_axi_last(2*i+j),
                        s_axis_cc_tkeep                   => pcie_cc_axi_keep(2*i+j),
                        s_axis_cc_tvalid                  => pcie_cc_axi_valid(2*i+j),
                        s_axis_cc_tready                  => s_axis_cc_tready(2*i+j),

                        pcie_rq_seq_num0                  => open,
                        pcie_rq_seq_num_vld0              => open,
                        pcie_rq_tag0                      => tag_assign_int(2*i+j)(7 downto 0),
                        pcie_rq_tag_vld0                  => tag_assign_vld_int(2*i+j)(0),
                        pcie_rq_tag1                      => tag_assign_int(2*i+j)(15 downto 8),
                        pcie_rq_tag_vld1                  => tag_assign_vld_int(2*i+j)(1),

                        pcie_cq_np_req                    => (others => '1'),
                        pcie_cq_np_req_count              => open,

                        cfg_phy_link_down                 => cfg_phy_link_down(2*i+j),
                        cfg_phy_link_status               => cfg_phy_link_status(2*i+j),
                        cfg_negotiated_width              => cfg_negotiated_width(2*i+j),
                        cfg_current_speed                 => cfg_current_speed(2*i+j),
                        cfg_max_payload                   => cfg_max_payload(2*i+j),
                        cfg_max_read_req                  => cfg_max_read_req(2*i+j),
                        cfg_function_status               => cfg_function_status(2*i+j),
                        cfg_function_power_state          => cfg_function_power_state(2*i+j),
                        cfg_vf_status                     => open,
                        cfg_vf_power_state                => open,
                        cfg_link_power_state              => cfg_link_power_state(2*i+j),
                        cfg_mgmt_addr                     => (others => '0'),
                        cfg_mgmt_function_number          => (others => '0'),
                        cfg_mgmt_write                    => '0',
                        cfg_mgmt_write_data               => (others => '0'),
                        cfg_mgmt_byte_enable              => (others => '0'),
                        cfg_mgmt_read                     => '0',
                        cfg_mgmt_read_data                => open,
                        cfg_mgmt_read_write_done          => open,
                        cfg_mgmt_debug_access             => '0',
                        cfg_err_cor_out                   => open,
                        cfg_err_nonfatal_out              => open,
                        cfg_err_fatal_out                 => open,
                        cfg_local_error_valid             => cfg_local_error_valid(2*i+j),
                        cfg_local_error_out               => cfg_local_error_out(2*i+j),
                        cfg_ltssm_state                   => cfg_ltssm_state(2*i+j),
                        cfg_rx_pm_state                   => cfg_rx_pm_state(2*i+j),
                        cfg_tx_pm_state                   => cfg_tx_pm_state(2*i+j),
                        cfg_rcb_status                    => cfg_rcb_status(2*i+j),
                        cfg_obff_enable                   => open,
                        cfg_pl_status_change              => open,
                        cfg_tph_requester_enable          => open,
                        cfg_tph_st_mode                   => open,
                        cfg_vf_tph_requester_enable       => open,
                        cfg_vf_tph_st_mode                => open,
                        cfg_dsn                           => (others => '0'),
                        cfg_bus_number                    => open,
                        cfg_msg_received                  => open,
                        cfg_msg_received_data             => open,
                        cfg_msg_received_type             => open,
                        cfg_msg_transmit                  => '0',
                        cfg_msg_transmit_type             => (others => '0'),
                        cfg_msg_transmit_data             => (others => '0'),
                        cfg_msg_transmit_done             => open,
                        cfg_fc_ph                         => dbg_credits_ph (2*i+j),
                        cfg_fc_pd                         => dbg_credits_pd (2*i+j),
                        cfg_fc_nph                        => dbg_credits_nph(2*i+j),
                        cfg_fc_npd                        => dbg_credits_npd(2*i+j),
                        cfg_fc_cplh                       => open,
                        cfg_fc_cpld                       => open,
                        cfg_fc_sel                        => (others => '0'),
                        cfg_power_state_change_ack        => '0',
                        cfg_power_state_change_interrupt  => open,
                        cfg_err_cor_in                    => '0',
                        cfg_err_uncor_in                  => '0',
                        cfg_flr_in_process                => open,
                        cfg_flr_done                      => (others => '0'),
                        cfg_vf_flr_in_process             => open,
                        cfg_vf_flr_func_num               => (others => '0'),
                        cfg_vf_flr_done                   => (others => '0'),
                        cfg_link_training_enable          => '1',
                        cfg_ext_read_received             => cfg_ext_read(2*i+j),
                        cfg_ext_write_received            => cfg_ext_write(2*i+j),
                        cfg_ext_register_number           => cfg_ext_register(2*i+j),
                        cfg_ext_function_number           => cfg_ext_function(2*i+j),
                        cfg_ext_write_data                => cfg_ext_write_data(2*i+j),
                        cfg_ext_write_byte_enable         => cfg_ext_write_be(2*i+j),
                        cfg_ext_read_data                 => cfg_ext_read_data(2*i+j),
                        cfg_ext_read_data_valid           => cfg_ext_read_dv(2*i+j),
                        cfg_interrupt_int                 => (others => '0'),
                        cfg_interrupt_pending             => (others => '0'),
                        cfg_interrupt_sent                => open,
                        cfg_interrupt_msi_sent            => open,
                        cfg_interrupt_msi_fail            => open,
                        cfg_interrupt_msi_function_number => (others => '0'),
                        cfg_interrupt_msix_enable         => open,
                        cfg_interrupt_msix_mask           => open,
                        cfg_interrupt_msix_vf_enable      => open,
                        cfg_interrupt_msix_vf_mask        => open,
                        cfg_interrupt_msix_data           => (others => '0'),
                        cfg_interrupt_msix_address        => (others => '0'),
                        cfg_interrupt_msix_int            => '0',
                        cfg_interrupt_msix_vec_pending    => (others => '0'),
                        cfg_interrupt_msix_vec_pending_status => open,
                        cfg_pm_aspm_l1_entry_reject       => '0',
                        cfg_pm_aspm_tx_l0s_entry_disable  => '0',
                        cfg_hot_reset_out                 => open,
                        cfg_config_space_enable           => '1',
                        cfg_req_pm_transition_l23_ready   => '0',
                        cfg_hot_reset_in                  => '0',
                        cfg_ds_port_number                => (others => '0'),
                        cfg_ds_bus_number                 => (others => '0'),
                        cfg_ds_device_number              => (others => '0'),
                        phy_rdy_out                       => pcie_phy_rdy_out(2*i+j)
                    );
                end generate;
            end generate;
        end generate;
    end generate;

    -- =========================================================================
    --  PCIE ADAPTER
    -- =========================================================================

    pcie_adapter_g : for i in 0 to PCIE_ENDPOINTS-1 generate
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
            ENDPOINT_TYPE      => ENDPOINT_TYPE,
            DEVICE             => DEVICE,
            AXI_CQUSER_WIDTH   => AXI_CQUSER_WIDTH,
            AXI_CCUSER_WIDTH   => AXI_CCUSER_WIDTH,
            AXI_RQUSER_WIDTH   => AXI_RQUSER_WIDTH,
            AXI_RCUSER_WIDTH   => AXI_RCUSER_WIDTH,
            AXI_STRADDLING     => false
        )
        port map (
            PCIE_CLK            => pcie_clk(i),
            PCIE_RESET          => pcie_rst(i)(0),
    
            AVST_DOWN_DATA      => (others => '0'),
            AVST_DOWN_HDR       => (others => '0'),
            AVST_DOWN_PREFIX    => (others => '0'),
            AVST_DOWN_SOP       => (others => '0'),
            AVST_DOWN_EOP       => (others => '0'),
            AVST_DOWN_EMPTY     => (others => '0'),
            AVST_DOWN_BAR_RANGE => (others => '0'),
            AVST_DOWN_VALID     => (others => '0'),
            AVST_DOWN_READY     => open,
    
            AVST_UP_DATA        => open,
            AVST_UP_HDR         => open,
            AVST_UP_PREFIX      => open,
            AVST_UP_SOP         => open,
            AVST_UP_EOP         => open,
            AVST_UP_ERROR       => open,
            AVST_UP_VALID       => open,
            AVST_UP_READY       => '0',
    
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
    
            CQ_AXI_DATA         => pcie_cq_axi_data(i),
            CQ_AXI_USER         => pcie_cq_axi_user(i),
            CQ_AXI_LAST         => pcie_cq_axi_last(i),
            CQ_AXI_KEEP         => pcie_cq_axi_keep(i),
            CQ_AXI_VALID        => pcie_cq_axi_valid(i),
            CQ_AXI_READY        => pcie_cq_axi_ready(i),

            RC_AXI_DATA         => pcie_rc_axi_data(i),
            RC_AXI_USER         => pcie_rc_axi_user(i),
            RC_AXI_LAST         => pcie_rc_axi_last(i),
            RC_AXI_KEEP         => pcie_rc_axi_keep(i),
            RC_AXI_VALID        => pcie_rc_axi_valid(i),
            RC_AXI_READY        => pcie_rc_axi_ready(i),

            CC_AXI_DATA         => pcie_cc_axi_data(i),
            CC_AXI_USER         => pcie_cc_axi_user(i),
            CC_AXI_LAST         => pcie_cc_axi_last(i),
            CC_AXI_KEEP         => pcie_cc_axi_keep(i),
            CC_AXI_VALID        => pcie_cc_axi_valid(i),
            CC_AXI_READY        => pcie_cc_axi_ready(i),

            RQ_AXI_DATA         => pcie_rq_axi_data(i),
            RQ_AXI_USER         => pcie_rq_axi_user(i),
            RQ_AXI_LAST         => pcie_rq_axi_last(i),
            RQ_AXI_KEEP         => pcie_rq_axi_keep(i),
            RQ_AXI_VALID        => pcie_rq_axi_valid(i),
            RQ_AXI_READY        => pcie_rq_axi_ready(i),
    
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
    --  PCIE RESET LOGIC
    -- =========================================================================

    pcie_rst_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        pcie_rst_async(i) <= pcie_hip_rst(i) or not user_lnk_up(i);

        pcie_rst_sync_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true,
            REPLICAS => RESET_WIDTH+1
        )
        port map (
            CLK       => pcie_clk(i),
            ASYNC_RST => pcie_rst_async(i),
            OUT_RST   => pcie_rst(i)
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
                PCIE_LINK_UP(i)  <= cfg_phy_link_status(i)(0) and cfg_phy_link_status(i)(1);
                PCIE_RCB_SIZE(i) <= cfg_rcb_status(i)(0);
                PCIE_MRRS(i)     <= cfg_max_read_req(i);
                PCIE_MPS(i)      <= '0' & cfg_max_payload(i);
            end if;
        end process;
        PCIE_EXT_TAG_EN(i)     <= '1';
        PCIE_10B_TAG_REQ_EN(i) <= '0';
    end generate;

    -- =========================================================================
    --  PCI EXT CAP - DEVICE TREE
    -- =========================================================================

    dt_g : for i in 0 to PCIE_ENDPOINTS-1 generate
        constant dt_en : boolean := (i = 0);
    begin
        -- Device Tree ROM
        pci_ext_cap_i: entity work.PCI_EXT_CAP
        generic map(
            ENDPOINT_ID            => i,
            ENDPOINT_ID_ENABLE     => true,
            DEVICE_TREE_ENABLE     => dt_en,
            VSEC_BASE_ADDRESS      => VSEC_BASE_ADDRESS,
            VSEC_NEXT_POINTER      => DTB_NEXT_POINTER,
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
            CFG_EXT_READ_DATA      => cfg_ext_read_dtb_data(i),
            CFG_EXT_READ_DV        => cfg_ext_read_dtb_dv(i)
        );

        xvc_g: if (XVC_ENABLE) generate
            xvc_i : xvc_vsec
            port map (
                clk                              => pcie_clk(i),
                pcie3_cfg_ext_function_number    => cfg_ext_function(i),
                pcie3_cfg_ext_read_data          => cfg_ext_read_xvc_data(i),
                pcie3_cfg_ext_read_data_valid    => cfg_ext_read_xvc_dv(i),
                pcie3_cfg_ext_read_received      => cfg_ext_read(i),
                pcie3_cfg_ext_register_number    => cfg_ext_register(i),
                pcie3_cfg_ext_write_byte_enable  => cfg_ext_write_be(i),
                pcie3_cfg_ext_write_data         => cfg_ext_write_data(i),
                pcie3_cfg_ext_write_received     => cfg_ext_write(i)
            );
        end generate;

        cfg_ext_read_dv(i) <= cfg_ext_read_dtb_dv(i) or cfg_ext_read_xvc_dv(i);
        cfg_ext_read_data(i) <= cfg_ext_read_xvc_data(i) when (cfg_ext_read_xvc_dv(i) = '1') else cfg_ext_read_dtb_data(i);
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
                MI_M_DWR  => mi_split_dwr (pe),
                MI_M_ADDR => mi_split_addr(pe),
                MI_M_RD   => mi_split_rd  (pe),
                MI_M_WR   => mi_split_wr  (pe),
                MI_M_BE   => mi_split_be  (pe),
                MI_M_DRD  => mi_split_drd (pe),
                MI_M_ARDY => mi_split_ardy(pe),
                MI_M_DRDY => mi_split_drdy(pe),

                CLK_S     => pcie_hip_clk (pe),
                RESET_S   => pcie_hip_rst (pe),
                MI_S_DWR  => mi_sync_dwr  (pe),
                MI_S_ADDR => mi_sync_addr (pe),
                MI_S_RD   => mi_sync_rd   (pe),
                MI_S_WR   => mi_sync_wr   (pe),
                MI_S_BE   => mi_sync_be   (pe),
                MI_S_DRD  => mi_sync_drd  (pe),
                MI_S_ARDY => mi_sync_ardy (pe),
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
                PIPE_OUT   => (others => false) ,
                DEVICE     => DEVICE
            )
            port map(
                CLK     => pcie_hip_clk     (pe),
                RESET   => pcie_hip_rst     (pe),

                RX_DWR  => mi_sync_dwr      (pe),
                RX_ADDR => mi_sync_addr     (pe),
                RX_BE   => mi_sync_be       (pe),
                RX_RD   => mi_sync_rd       (pe),
                RX_WR   => mi_sync_wr       (pe),
                RX_ARDY => mi_sync_ardy     (pe),
                RX_DRD  => mi_sync_drd      (pe),
                RX_DRDY => mi_sync_drdy     (pe),

                TX_DWR  => mi_split_dbg_dwr (pe),
                TX_ADDR => mi_split_dbg_addr(pe),
                TX_BE   => mi_split_dbg_be  (pe),
                TX_RD   => mi_split_dbg_rd  (pe),
                TX_WR   => mi_split_dbg_wr  (pe),
                TX_ARDY => mi_split_dbg_ardy(pe),
                TX_DRD  => mi_split_dbg_drd (pe),
                TX_DRDY => mi_split_dbg_drdy(pe)
            );

            -- -----------------------------------------------
            --  Streaming Debug Master for each PCIe Endpoint
            -- -----------------------------------------------
            debug_master_i : entity work.STREAMING_DEBUG_MASTER
            generic map(
                CONNECTED_PROBES   => DBG_PROBES    ,
                REGIONS            => RQ_MFB_REGIONS,
                DEBUG_ENABLED      => true          ,
                PROBE_ENABLED      => "E"           ,
                COUNTER_WORD       => "E"           ,
                COUNTER_WAIT       => "E"           ,
                COUNTER_DST_HOLD   => "E"           ,
                COUNTER_SRC_HOLD   => "E"           ,
                COUNTER_SOP        => "D"           , -- disabled
                COUNTER_EOP        => "D"           , -- disabled
                BUS_CONTROL        => "D"           , -- disabled
                PROBE_NAMES        => DBG_PROBE_STR ,
                DEBUG_REG          => true
            )
            port map(
                CLK           => pcie_hip_clk     (pe)   ,
                RESET         => pcie_hip_rst     (pe)   ,

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
                DEBUG_SRC_RDY => debug_src_rdy    (pe)   ,
                DEBUG_DST_RDY => debug_dst_rdy    (pe)
            );

            -- PERQ (PCIe Endpoint RQ) - pcie_rq_axi signals
            debug_probe_i : entity work.STREAMING_DEBUG_PROBE_MFB
            generic map(
                REGIONS => RQ_MFB_REGIONS
            )
            port map(
                RX_SOF         => (others => '0')         , -- SOP counters are unecessary => disabled in the Master Probe
                RX_EOF         => (others => '0')         , -- EOP counters are unecessary => disabled in the Master Probe
                RX_SRC_RDY     => pcie_rq_axi_valid(pe)   ,
                RX_DST_RDY     => open                    ,

                TX_SOF         => open                    ,
                TX_EOF         => open                    ,
                TX_SRC_RDY     => open                    ,
                TX_DST_RDY     => pcie_rq_axi_ready(pe)   ,

                DEBUG_BLOCK    => '0'                     ,
                DEBUG_DROP     => '0'                     ,
                DEBUG_SOF      => open                    ,
                DEBUG_EOF      => open                    ,
                DEBUG_SRC_RDY  => debug_src_rdy    (pe)(0),
                DEBUG_DST_RDY  => debug_dst_rdy    (pe)(0)
            );

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
                    CLK       => pcie_hip_clk     (pe)      ,
                    RESET     => pcie_hip_rst     (pe)      ,

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
            process (pcie_hip_clk(pe))
            begin
                if (rising_edge(pcie_hip_clk(pe))) then
                    eve_ph(pe)(0)  <= '1' when (unsigned(dbg_credits_ph(pe)) >= 0 ) and (unsigned(dbg_credits_ph(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_ph(pe)(1)  <= '1' when (unsigned(dbg_credits_ph(pe)) >= 8 ) and (unsigned(dbg_credits_ph(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_ph(pe)(2)  <= '1' when (unsigned(dbg_credits_ph(pe)) >= 32) and (unsigned(dbg_credits_ph(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_ph(pe)(3)  <= dbg_credits_ph(pe)(7);                                                                            -- 127+   available Descriptors
                    eve_ph_reg(pe) <= eve_ph(pe);
                end if;
            end process;

            -- Posted Data
            process (pcie_hip_clk(pe))
            begin
                if (rising_edge(pcie_hip_clk(pe))) then
                    eve_pd(pe)(0)  <= '1' when (unsigned(dbg_credits_pd(pe)) >= 0 ) and (unsigned(dbg_credits_pd(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_pd(pe)(1)  <= '1' when (unsigned(dbg_credits_pd(pe)) >= 8 ) and (unsigned(dbg_credits_pd(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_pd(pe)(2)  <= '1' when (unsigned(dbg_credits_pd(pe)) >= 32) and (unsigned(dbg_credits_pd(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_pd(pe)(3)  <= or dbg_credits_pd(pe)(dbg_credits_pd'high downto 7);                                              -- 127+   available Descriptors
                    eve_pd_reg(pe) <= eve_pd(pe);
                end if;
            end process;

            -- Non-Posted Headers
            process (pcie_hip_clk(pe))
            begin
                if (rising_edge(pcie_hip_clk(pe))) then
                    eve_nph(pe)(0)  <= '1' when (unsigned(dbg_credits_nph(pe)) >= 0 ) and (unsigned(dbg_credits_nph(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_nph(pe)(1)  <= '1' when (unsigned(dbg_credits_nph(pe)) >= 8 ) and (unsigned(dbg_credits_nph(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_nph(pe)(2)  <= '1' when (unsigned(dbg_credits_nph(pe)) >= 32) and (unsigned(dbg_credits_nph(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_nph(pe)(3)  <= dbg_credits_nph(pe)(7);                                                                             -- 127+   available Descriptors
                    eve_nph_reg(pe) <= eve_nph(pe);
                end if;
            end process;

            -- Non-Posted Data
            process (pcie_hip_clk(pe))
            begin
                if (rising_edge(pcie_hip_clk(pe))) then
                    eve_npd(pe)(0)  <= '1' when (unsigned(dbg_credits_npd(pe)) >= 0 ) and (unsigned(dbg_credits_npd(pe)) <= 7  ) else '0'; -- 0-7    available Descriptors
                    eve_npd(pe)(1)  <= '1' when (unsigned(dbg_credits_npd(pe)) >= 8 ) and (unsigned(dbg_credits_npd(pe)) <= 31 ) else '0'; -- 8-31   available Descriptors
                    eve_npd(pe)(2)  <= '1' when (unsigned(dbg_credits_npd(pe)) >= 32) and (unsigned(dbg_credits_npd(pe)) <= 127) else '0'; -- 32-127 available Descriptors
                    eve_npd(pe)(3)  <= or dbg_credits_npd(pe)(dbg_credits_npd'high downto 7);                                              -- 127+   available Descriptors
                    eve_npd_reg(pe) <= eve_npd(pe);
                end if;
            end process;

        end generate;

    end generate;

end architecture;
