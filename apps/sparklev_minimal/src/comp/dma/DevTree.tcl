# 1.  base - base module address
# 2.  type - controller type: 4 for DMA Calypte
# 3.  rxn  - number of RX channels
# 4.  txn  - number of TX channels
# 5.  pcie - index(es) of PCIe endpoint(s) which DMA module uses.
# 6.  rx_frame_size_max - maximum allowed size of DMA RX frame
# 7.  tx_frame_size_max - maximum allowed size of DMA TX frame
# 8.  rx_frame_size_min - minimum allowed size of DMA RX frame
# 9.  tx_frame_size_min - minimum allowed size of DMA TX frame
# 10. dbg_en - enabled debug logic for DMA (if there is one fs)
# 11. offset - address offset for TX controllers
proc dts_dmamod_open {base type rxn txn pcie rx_frame_size_max tx_frame_size_max rx_frame_size_min tx_frame_size_min dbg_en {offset 0x00200000}} {
    set    ret ""
    append ret "dma_module@$base {"

    append ret "#address-cells = <1>;"
    append ret "#size-cells = <1>;"

    if {$type != 4} {
        error "ERROR: Unsupported DMA Type: $type for DMA Module!"
    }

    if {$rxn > 0} {
        append ret "dma_params_rx$pcie:" [dts_dma_params "dma_params_rx$pcie" $rx_frame_size_max $rx_frame_size_min]
    }

    if {$txn > 0} {
        append ret "dma_params_tx$pcie:" [dts_dma_params "dma_params_tx$pcie" $tx_frame_size_max $tx_frame_size_min]
    }

    # RX DMA Channels
    for {set i 0} {$i < $rxn} {incr i} {
        # if {$dbg_en} {
        #     append ret [dts_event_counter [expr $base + 0x00010000 + $i * 0x80 + 0x00] "event_counter0_$i" 1]
        #     append ret [dts_event_counter [expr $base + 0x00010000 + $i * 0x80 + 0x10] "event_counter1_$i" 1]
        #     append ret [dts_event_counter [expr $base + 0x00010000 + $i * 0x80 + 0x20] "event_counter2_$i" 1]
        # }
        set    var_base [expr $base + $i * 0x80]
        dts_dma_calypte_ctrl ret "rx" $i $var_base $pcie
    }

    # TX DMA channels
    for {set i 0} {$i < $txn} {incr i} {
        set    var_base [expr $base + $i * 0x80 + $offset]
        dts_dma_calypte_ctrl ret "tx" $i $var_base $pcie
    }

    if {$type == 4} {
        dts_calypte_test_core ret [expr $base + "0x300000"] $dma_debug_enable
    }

    append ret "};"
    return $ret
}

# 1. name - node name
# 2. frame_size_max - maximum allowed size of DMA frame
# 3. frame_size_min - minimum allowed size of DMA frame
proc dts_dma_params {name frame_size_max frame_size_min} {
    set ret ""
    append ret "$name {"
    append ret "frame_size_max = <$frame_size_max>;"
    append ret "frame_size_min = <$frame_size_min>;"
    append ret "};"
    return $ret
}
