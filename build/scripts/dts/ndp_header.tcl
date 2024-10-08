proc dts_ndp_header {dir id items {len ""}} {
    set ret ""
    append ret "ndp_header_${dir}${id} {"
    append ret "compatible = \"cesnet,ofm,ndp-header-${dir}\", \"cesnet,ofm,packed-item\";"
    append ret "header_id = <$id>;"
    # Length of the complete header in [B] (optional)
    if {$len != ""} {append ret "header_length = <$len>;"}
    append ret [dts_packed_item $items]
    append ret "};"
    return $ret
}
