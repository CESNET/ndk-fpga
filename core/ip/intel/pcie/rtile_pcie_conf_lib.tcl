# rtile_conf_lib.tcl: R-Tile PCIe IP configuration library.
# Copyright (C) 2025 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc do_rtile_pcie_gen5_2x8 {pci_vendor_id pci_device_id usr_clkfreq} {
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_device_id_hwtcl $pci_device_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_vendor_id_user_hwtcl $pci_vendor_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 core8_pf0_pci_type0_device_id_hwtcl $pci_device_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 core8_pf0_pci_type0_vendor_id_user_hwtcl $pci_vendor_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cap_slot_clk_config_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_addr_size0_attr_user_hwtcl} {767}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_pf_en0_attr_user_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_cii_range_0_k_cii_start_addr0_attr_user_hwtcl} {3328}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_enable_cii_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar0_address_width_user_hwtcl} {26}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar0_type_user_hwtcl} {64-bit non-prefetchable memory}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar2_address_width_user_hwtcl} {24}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_bar2_type_user_hwtcl} {64-bit non-prefetchable memory}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_class_code_hwtcl} {131072}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_pf0_gen2_ctrl_off_support_mod_ts_hwtcl} {0}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_user_vsec_cap_enable_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core8_virtual_pf0_user_vsec_offset_hwtcl} {3328}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {top_topology_hwtcl} {Gen5 2x8, Interface - 512 bit}
    set_instance_parameter_value intel_rtile_pcie_ast_0 g5_pld_clkfreq_user_hwtcl $usr_clkfreq

    set_interface_property p1_rx_st0 EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st0
    set_interface_property p1_rx_st_misc EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st_misc
    set_interface_property p1_rx_st1 EXPORT_OF intel_rtile_pcie_ast_0.p1_rx_st1
    set_interface_property p1_tx_st_misc EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st_misc
    set_interface_property p1_tx_st0 EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st0
    set_interface_property p1_tx_st1 EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_st1
    set_interface_property p1_tx_ehp EXPORT_OF intel_rtile_pcie_ast_0.p1_tx_ehp
    set_interface_property p1_reset_status_n EXPORT_OF intel_rtile_pcie_ast_0.p1_reset_status_n
    set_interface_property p1_slow_reset_status_n EXPORT_OF intel_rtile_pcie_ast_0.p1_slow_reset_status_n
    set_interface_property p1_hip_status EXPORT_OF intel_rtile_pcie_ast_0.p1_hip_status
    set_interface_property p1_power_mgnt EXPORT_OF intel_rtile_pcie_ast_0.p1_power_mgnt
    set_interface_property p1_pld_gp EXPORT_OF intel_rtile_pcie_ast_0.p1_pld_gp
    set_interface_property p1_cii EXPORT_OF intel_rtile_pcie_ast_0.p1_cii
}

proc do_rtile_pcie_gen5_1x16 {pci_vendor_id pci_device_id usr_clkfreq} {
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_device_id_hwtcl $pci_device_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_vendor_id_user_hwtcl $pci_vendor_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 {top_topology_hwtcl} {Gen5 1x16, Interface - 1024 bit}
    set_instance_parameter_value intel_rtile_pcie_ast_0 g5_pld_clkfreq_user_hwtcl $usr_clkfreq
}

proc do_rtile_pcie_gen4_1x16 {pci_vendor_id pci_device_id usr_clkfreq} {
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_device_id_hwtcl $pci_device_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 core16_pf0_pci_type0_vendor_id_user_hwtcl $pci_vendor_id
    set_instance_parameter_value intel_rtile_pcie_ast_0 {top_topology_hwtcl} {Gen4 1x16, Interface - 512 bit}
    set_instance_parameter_value intel_rtile_pcie_ast_0 g4_pld_clkfreq_single_user_hwtcl $usr_clkfreq
}

proc do_rtile_pcie_common {} {
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cap_slot_clk_config_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_addr_size0_attr_user_hwtcl} {767}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_pf_en0_attr_user_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_cii_range_0_k_cii_start_addr0_attr_user_hwtcl} {3328}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_enable_cii_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar0_address_width_user_hwtcl} {26}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar0_type_user_hwtcl} {64-bit non-prefetchable memory}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar2_address_width_user_hwtcl} {24}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_bar2_type_user_hwtcl} {64-bit non-prefetchable memory}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_pf0_class_code_hwtcl} {131072}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_user_vsec_cap_enable_hwtcl} {1}
    set_instance_parameter_value intel_rtile_pcie_ast_0 {core16_virtual_pf0_user_vsec_offset_hwtcl} {3328}

    set_interface_property p0_cii EXPORT_OF intel_rtile_pcie_ast_0.p0_cii
}
