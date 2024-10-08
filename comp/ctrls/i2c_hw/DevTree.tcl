# 1. no   - numero sign of i2c bus (order number of i2c in design)
# 2. base - base address of i2c for access
proc dts_i2c {no base} {
    set   size 0x8
    set    ret ""
    append ret "i2c$no {"
    append ret "compatible = \"netcope,i2c\";"
    append ret "reg = <$base $size>;"
    append ret "};"
    return $ret
}
