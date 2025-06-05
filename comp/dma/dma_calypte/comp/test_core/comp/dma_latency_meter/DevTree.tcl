# DevTree.tcl: generate nodes for the DMA latecny meter
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Vladisav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc dts_dma_latency_meter {DTS base_addr {idx 0}} {
    upvar 1 $DTS dts

    dts_create_node dts "dma_latency_meter$idx" {
        dts_appendprop_comp_node dts $base_addr 0x30 "cesnet,dma_latency_meter"
    }
}
