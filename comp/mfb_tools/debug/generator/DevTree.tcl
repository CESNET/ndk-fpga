# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
proc dts_mfb_generator {base name} {
    set size 0x40
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,mfb_generator\";"
    append ret "reg = <$base $size>;"
    append ret "version = <1>;"
    append ret "};"
    return $ret
}
