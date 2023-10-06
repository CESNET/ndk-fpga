# Modules.tcl: script to compile single module
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# converting input list to associative array (uncomment when needed)
array set ARCHGRP_ARR $ARCHGRP

# Component paths
set MI_ASYNC_BASE       "$OFM_PATH/comp/mi_tools/async"
set MFB_META_INS_BASE   "$OFM_PATH/comp/mfb_tools/flow/metadata_insertor"
set MFB_META_EXT_BASE   "$OFM_PATH/comp/mfb_tools/flow/metadata_extractor"
set APP_CORE_UTILS_BASE "$OFM_PATH/../core/intel/src/comp/app_core_utils"

# Packages
lappend PACKAGES "$ENTITY_BASE/many_core_package.vhd"
lappend PACKAGES "$ENTITY_BASE/RISCV_package.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

if {$ARCHGRP_ARR(APP_CORE_ENABLE)} {

    set regex {v(\d+\.\d+)}

    set command_output [exec {*}[list vivado -version]]
    set tool_version ""

    if {![regexp $regex "$command_output" match tool_version]} {
        error "Cannot determine Vivado version"
    }

    # Components
    lappend COMPONENTS [ list "MI_ASYNC"                $MI_ASYNC_BASE       "FULL" ]
    lappend COMPONENTS [ list "MFB_METADATA_INSERTOR"   $MFB_META_INS_BASE   "FULL" ]
    lappend COMPONENTS [ list "MFB_METADATA_EXTRACTOR"  $MFB_META_EXT_BASE   "FULL" ]

    # Files

    if {$tool_version == "2022.2"} {
        lappend MOD "$ENTITY_BASE/mult.xci"
    } elseif {$tool_version == "2021.2"} {
        lappend MOD "$ENTITY_BASE/old_vivado_ip/mult.xci"
    }

    lappend MOD "$ENTITY_BASE/barrel_core_variant_1.vhd"
    lappend MOD "$ENTITY_BASE/barrel_core_variant_1_mult.vhd"
    lappend MOD "$ENTITY_BASE/barrel_core_variant_2.vhd"
    lappend MOD "$ENTITY_BASE/barrel_core_variant_2_mult.vhd"
    lappend MOD "$ENTITY_BASE/barrel_core_variant_3.vhd"
    lappend MOD "$ENTITY_BASE/barrel_core_variant_3_mult.vhd"
    lappend MOD "$ENTITY_BASE/instr_rom.vhd"
    lappend MOD "$ENTITY_BASE/instr_data_mem_combi.vhd"
    lappend MOD "$ENTITY_BASE/fifo.vhd"
    lappend MOD "$ENTITY_BASE/dual_port_byte_en_RAM.vhd"
    lappend MOD "$ENTITY_BASE/many_core_system.vhd"
    lappend MOD "$ENTITY_BASE/barrel_proc_debug_core.vhd"
    lappend MOD "$ENTITY_BASE/app_subcore.vhd"
    lappend MOD "$ENTITY_BASE/app_subcore_tb.vhd"
    lappend MOD "$ENTITY_BASE/application_core.vhd"
    
} else {
    lappend MOD "$APP_CORE_UTILS_BASE/app_core_empty_arch.vhd"
}

lappend MOD "$ENTITY_BASE/DevTree.tcl"
