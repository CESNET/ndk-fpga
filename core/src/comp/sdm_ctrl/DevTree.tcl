# 1. base    - base address on MI bus
# 2. boot_en - use controller for boot in Active Serial configuration scheme
proc dts_sdm_controller {base boot_en} {
    set    ret ""
    append ret "intel_sdm_controller {"
    append ret "compatible = \"netcope,intel_sdm_controller\";"
    append ret "reg = <$base 44>;"
    append ret "type = <0>;"
    append ret "version = <0x00000001>;"
    append ret "boot_en = <$boot_en>;"
    append ret "};"
    return $ret
}
