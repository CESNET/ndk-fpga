proc dts_timestamp_limiter {base ts_format sel_qs} {
    set    ret ""
    append ret "timestamp_limiter {"
    append ret "compatible = \"cesnet,ofm,timestamp_limiter\";"
    append ret "version = <0x00000001>;"
    append ret "reg = <$base 0x10>;"
    append ret "timestamp_format = <$ts_format>;"
    append ret "selected_queues = <$sel_qs>;"
    append ret "};"
    return $ret
}
