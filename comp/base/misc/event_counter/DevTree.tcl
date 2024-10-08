# 1. base - base address on MI bus
# 2. name - instantion name inside device tree hierarchy
# 3. cap_en - is FIFO capture enabled?
proc dts_event_counter {base name cap_en} {
    set    ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,event_counter\";"
    if {$cap_en} {append ret "fifo_capture_enabled;"}
    append ret "version = <0x00000001>;"
    append ret "reg = <$base 0x10>;"
    append ret "};"
    return $ret
}
