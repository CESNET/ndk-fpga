# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
proc dts_gen_loop_switch {base name} {
    set size 0x200
    # At the DMA_RX interface
    set l2r_tx_sm_base [expr $base + 0x40]
    # At the DMA_TX interface
    set r2l_rx_sm_base [expr $base + 0x50]
    # At the ETH_RX interface
    set l2r_rx_sm_base [expr $base + 0x60]
    # At the ETH_TX interface
    set r2l_tx_sm_base [expr $base + 0x70]
    # Generators
    set gen2dma_base [expr $base + 0x80]
    set gen2eth_base [expr $base + 0xC0]
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,gen_loop_switch\";"
    append ret "reg = <$base $size>;"
    append ret "version = <1>;"
    append ret [dts_speed_meter $l2r_tx_sm_base "l2r_tx_speed_meter"]
    append ret [dts_speed_meter $r2l_rx_sm_base "r2l_rx_speed_meter"]
    append ret [dts_speed_meter $l2r_rx_sm_base "l2r_rx_speed_meter"]
    append ret [dts_speed_meter $r2l_tx_sm_base "r2l_tx_speed_meter"]
    append ret [dts_mfb_generator $gen2dma_base "mfb_gen2dma"]
    append ret [dts_mfb_generator $gen2eth_base "mfb_gen2eth"]
    append ret "};"
    return $ret
}
