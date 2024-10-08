# 1. name - instantion name inside device tree hierarchy
# 2. base - base address on MI bus
proc dts_hbm_tester {name base} {
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,hbm_tester\";"
    append ret "reg = <$base 0x1000>;"
    append ret "};"
    return $ret
}
