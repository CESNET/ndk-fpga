# 1. name - instantion name inside device tree hierarchy
# 2. base - base address on MI bus
proc dts_mi_test_space {name base} {
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,mi_test_space\";"
    append ret "reg = <$base 0x100>;"
    append ret "};"
    return $ret
}
