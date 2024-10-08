# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set MI2AXI4_BASE "$OFM_PATH/comp/mi_tools/converters/mi2axi4"

# Components
lappend COMPONENTS [ list "MI2AXI4" $MI2AXI4_BASE "FULL" ]

# Search Path for custom Quartus IP
lappend SRCS(SEARCH_PATH) "$ENTITY_BASE/pmci_ip"

# Files
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/spi_master/avmms_2_spim_bridge.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/spi_master/altera_avalon_st_packets_to_bytes.v"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/spi_master/altera_avalon_st_bytes_to_packets.v"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/pmci_csr/pmci_csr.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/pxeboot_optrom/pxeboot_optrom.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/ncsi_ctrlr/ncsi_ctrlr.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ingr.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_egrs.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/mctp_pcievdm_ctrlr/mctp_pcievdm_ctrlr.sv"
lappend MOD "$ENTITY_BASE/pmci_ip/custom_ip/flash_burst_master/flash_burst_master.sv"

lappend MOD "$ENTITY_BASE/pmci_ip/pmci_ss.qsys"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_s10_mailbox_client_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_pxeboot_optrom_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_axi_bridge_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_axi_bridge_1.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_clock_in.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_mctp_pcievdm_ctrlr_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_intel_niosv_m_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_pmci_csr_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_avmms_2_spim_bridge_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_reset_in.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_spi_slave_to_avalon_mm_master_bridge_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_intel_generic_serial_flash_interface_top_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_onchip_memory2_1.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_onchip_memory2_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_flash_burst_master_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_ncsi_ctrlr_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_timer_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/ip/pmci_ss/pmci_ss_stratix10_asd_0.ip"
lappend MOD "$ENTITY_BASE/pmci_ip/pmci_ss_nios_fw.hex"

lappend MOD "$ENTITY_BASE/pmci_top.vhd"

lappend MOD "$ENTITY_BASE/DevTree.tcl"
