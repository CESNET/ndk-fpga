# DevTree.tcl: generate nodes for the test core
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Vladisav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc dts_calypte_test_core {DTS base_addr {dbg_en False} {idx 0}} {
    upvar 1 $DTS dts

    set LOOPBACK_BASE_ADDR      [expr $base_addr + 0x0]
    set TX_DBG_CORE_BASE_ADDR   [expr $base_addr + 0x10000]
    set LATENCY_METER_BASE_ADDR [expr $base_addr + 0x20000]
    set RESET_FSM_BASE_ADDR     [expr $base_addr + 0x30000]

    dts_create_node dts "dma_calypte_test_core$idx" {

        dts_create_node dts "mfb_loopback$idx" {
            dts_appendprop_comp_node dts $LOOPBACK_BASE_ADDR 8 "cesnet,mfb_loopback"
        }

        if ($dbg_en) {
            dts_create_node dts "dma_calypte_debug_core$idx" {
                dts_appendprop_comp_node dts $TX_DBG_CORE_BASE_ADDR 0x1600 "cesnet,dma_calypte_debug_core"

                dts_create_node dts "mfb_generator$idx" {
                    dts_appendprop_comp_node dts [expr $TX_DBG_CORE_BASE_ADDR+0x8000] 0x40 "cesnet,mfb_generator"
                }
            }

            dts_dma_latency_meter dts $LATENCY_METER_BASE_ADDR $idx
        }

        dts_create_node dts "dma_calypte_reset_fsm$idx" {
            dts_appendprop_comp_node dts $RESET_FSM_BASE_ADDR 0x4 "cesnet,dma_calypte_reset_fsm"
        }
    }
}
