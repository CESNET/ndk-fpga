proc dts_ofs_pmci {base} {
    set ret ""
    append ret "ofs_pmci {"
    append ret "compatible = \"cesnet,pmci\";"
    append ret "version = <0x00000001>;"
    append ret "reg = <$base 0x1000>;"
    append ret "};"
    return $ret
}
