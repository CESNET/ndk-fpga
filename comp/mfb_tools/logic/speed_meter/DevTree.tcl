proc dts_speed_meter {base {name "speed_meter"}} {
    set ret ""
    append ret "$name {"
    append ret "compatible = \"cesnet,ofm,speed_meter\";"
    append ret "version = <0x00000001>;"
    append ret "reg = <$base 0x20>;"
    append ret "};"
    return $ret
}
