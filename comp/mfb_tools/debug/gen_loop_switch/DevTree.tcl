# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
proc dts_gen_loop_switch {base name} {
    set size 0x200
    set gen2dma_base [expr $base + 0x80]
    set gen2eth_base [expr $base + 0xC0]
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,gen_loop_switch\";"
    append ret "reg = <$base $size>;"
    append ret "version = <1>;"
    append ret [dts_mfb_generator $gen2dma_base "mfb_gen2dma"]
    append ret [dts_mfb_generator $gen2eth_base "mfb_gen2eth"]
    append ret "};"
    return $ret
}
