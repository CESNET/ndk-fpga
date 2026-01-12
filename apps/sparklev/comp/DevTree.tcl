# DevTree.tcl: DevTree generation script for Sparklev Application
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

proc dts_application {DTS base} {
    upvar 1 $DTS dts

    dts_create_node dts "sparklev_conf_space" {
        dts_appendprop_comp_node dts $base 0x300 "ziti,sparklev,conf_space"
    }
}

proc dts_sparklev_main_mi {DTS dma_gen_loop_en pcie_eps pcie_debug_en pcie_endpoint_mode pcie_mod_arch} {
    upvar 1 $DTS ret

    # Boot module
    dts_ndk_core_boot_module ret

    # MI test space
    append ret [dts_mi_test_space "mi_test_space" $NdkCore::ADDR_TEST_SPACE]

    dts_application ret $NdkCore::ADDR_USERAPP

    # Gen Loop Switch debug modules for each DMA stream/module
    if {$dma_gen_loop_en} {
        for {set i 0} {$i < $pcie_eps} {incr i} {
            set    gls_offset [expr $i * 0x200]
            append ret [dts_gen_loop_switch [expr $NdkCore::ADDR_GEN_LOOP + $gls_offset] "dbg_gls$i"]
        }
    }

    # PCIe Debug
    if {$pcie_debug_en} {
        append ret [dts_pcie_core_dbg $NdkCore::ADDR_PCIE_DBG $pcie_eps $pcie_endpoint_mode $pcie_mod_arch]

        set pcie_ctrl_base [expr $NdkCore::ADDR_PCIE_DBG + "0x100000"]
        append ret [dts_pcie_ctrl_dbg $pcie_ctrl_base $pcie_eps $pcie_endpoint_mode $pcie_mod_arch]
    }
}

proc dts_build_project {} {
    global PCIE_ENDPOINTS H2C_DMA_CHANNELS C2H_DMA_CHANNELS DMA_PKT_SIZE_MAX DMA_DEBUG_ENABLE PCIE_DEBUG_ENABLE \
              PCIE_ENDPOINT_MODE PCIE_MOD_ARCH DMA_GEN_LOOP_EN H2C_DMA_PTR_WIDTH
    return [dts_build_netcope dts_sparklev_main_mi $PCIE_ENDPOINTS 4 $H2C_DMA_CHANNELS $C2H_DMA_CHANNELS $DMA_PKT_SIZE_MAX \
                $DMA_PKT_SIZE_MAX 60 60 $DMA_DEBUG_ENABLE $PCIE_DEBUG_ENABLE $PCIE_ENDPOINT_MODE $PCIE_MOD_ARCH \
                $DMA_GEN_LOOP_EN $H2C_DMA_PTR_WIDTH]
}
