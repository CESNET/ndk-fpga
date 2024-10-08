proc dts_packed_item {items} {
    set ret ""

    set names ""
    set offsets ""
    set widths ""

    set off 0
    foreach i $items {
        unset -nocomplain item_flags
        array set item_flags [lassign $i name width]

        if {$name != ""} {
            lappend names "\"$name\""
            lappend widths $width
            lappend offsets $off
        }

        if {![info exists item_flags(group)]} {
            incr off $width
        }
    }

    append ret "item-name  =  [join $names ", "];\n"
    append ret "item-width = /bits/ 16 <[join $widths]>;\n"
    append ret "item-offset= /bits/ 16 <[join $offsets]>;\n"

    return $ret
}
