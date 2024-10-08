proc dts_rate_limiter {base sec_len int_len max_ints speed} {
    # The default output speed in Gigabits per second
    # considering that the frequency of the APP clock is 200 MHz.
    # <speed (in Bytes per Section)> * <sections_per_second>; convert to bits per second; convert to Gbps
    set speed_gbps [expr $speed * (200000000 / $sec_len) * 8 / 1000000000]
    set ret ""
    append ret "rate_limiter {"
    append ret "compatible = \"cesnet,ofm,rate_limiter\";"
    append ret "version = <0x00000001>;"
    append ret "reg = <$base 0x100>;"
    append ret "maximum_intervals = <$max_ints>;"
    append ret "default_interval_len = <$int_len>;"
    append ret "default_section_len = <$sec_len>;"
    append ret "default_speed_gbps = <$speed_gbps>;"
    append ret "};"
    return $ret
}
