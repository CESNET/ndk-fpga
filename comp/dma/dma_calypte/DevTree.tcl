# dts_dma_calypte_ctrl parameters:
# 1. dir        - direction which to choose (rx or tx)
# 2. id         - channel ID
# 3. base       - base address of channel
# 4. pcie       - index(es) of PCIe endpoint(s) which DMA controller uses.
proc dts_dma_calypte_ctrl {DTS dir id base pcie} {
    upvar 1 $DTS dts

    dts_create_node dts "dma_ctrl_calypte_$dir$id" {
        dts_appendprop_comp_node dts $base 0x80 "cesnet,dma_ctrl_calypte_$dir"
        dts_appendprop_int dts "version" 0x10000
        dts_appendprop_int dts "pcie" $pcie
        if { $dir == "tx" } {
            append dts "data_buff = <&dma_calypte_tx_data_buff$id\_pcie$pcie>;"
            append dts "hdr_buff = <&dma_calypte_tx_hdr_buff$id\_pcie$pcie>;"
        }
        append dts "params = <&dma_params_$dir$pcie>;"
    }
}

# generates Device Tree entries for data buffers in DMA Calypte
# 1. type       - content of the buffer (header or data)
# 2. id         - channel ID
# 3. base       - base address for the buffer
# 4. size       - size of the buffer
# 5. pcie       - index(es) of PCIe endpoint(s) which DMA controller uses.
proc dts_dma_calypte_tx_buffer {DTS type id base size pcie} {
    upvar 1 $DTS dts

    dts_create_labeled_node dts "dma_calypte_tx_${type}_buff${id}_pcie${pcie}" "dma_calypte_tx_${type}_buff${id}" {
        dts_appendprop_comp_node dts $base $size "cesnet,dma_calypte_tx_${type}_buff"
        dts_appendprop_int dts "pcie" $pcie
    }
}

# Adds a node to the Device Tree for performance counters within DMA Calypte
# 1. DTS - reference to DeviceTree string
# 2. Base - base address of the registers in the MI address space
proc dts_dma_perf_cntrs {DTS base} {
    upvar 1 $DTS dts

    dts_create_node dts "dma_calypte_rx_perf_cntrs0" {
        dts_appendprop_comp_node dts $base 0x30 "cesnet,dma_calypte_rx_perf_cntrs"
    }
}
