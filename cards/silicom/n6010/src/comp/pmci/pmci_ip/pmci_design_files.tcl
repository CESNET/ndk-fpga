# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

#
# PMCI
#--------------------

set_global_assignment -name SEARCH_PATH "$::env(BUILD_ROOT_REL)/ipss"

set vlog_macros [get_all_global_assignments -name VERILOG_MACRO]
set include_pmci 0

foreach_in_collection m $vlog_macros {
    if { [string equal "INCLUDE_PMCI" [lindex $m 2]] } {
        set include_pmci 1
        break
    }
}

if {$include_pmci == 1} {
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/spi_master/avmms_2_spim_bridge.sv
    set_global_assignment -name VERILOG_FILE             $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/spi_master/altera_avalon_st_packets_to_bytes.v
    set_global_assignment -name VERILOG_FILE             $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/spi_master/altera_avalon_st_bytes_to_packets.v
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/pmci_csr/pmci_csr.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/pxeboot_optrom/pxeboot_optrom.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/ncsi_ctrlr/ncsi_ctrlr.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ingr.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_egrs.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ctrlr.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/custom_ip/flash_burst_master/flash_burst_master.sv
    set_global_assignment -name SYSTEMVERILOG_FILE       $::env(BUILD_ROOT_REL)/ipss/pmci/pmci_wrapper.sv

    set_global_assignment -name QSYS_FILE                $::env(BUILD_ROOT_REL)/ipss/pmci/pmci_ss.qsys
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_s10_mailbox_client_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_axi_bridge_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_axi_bridge_1.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_clock_in.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_mctp_pcievdm_ctrlr_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_intel_niosv_m_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_pmci_csr_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_pxeboot_optrom_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_avmms_2_spim_bridge_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_reset_in.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_spi_slave_to_avalon_mm_master_bridge_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_intel_generic_serial_flash_interface_top_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_onchip_memory2_1.ip
    set_global_assignment -name HEX_FILE                 $::env(BUILD_ROOT_REL)/ipss/pmci/pmci_ss_nios_fw.hex
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_onchip_memory2_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_flash_burst_master_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_ncsi_ctrlr_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_timer_0.ip
    set_global_assignment -name IP_FILE                  $::env(BUILD_ROOT_REL)/ipss/pmci/ip/pmci_ss/pmci_ss_stratix10_asd_0.ip
}
