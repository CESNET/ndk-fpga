# 1. base - base address on MI bus
# 2. endpoints - number of PCIe endpoints
# 3. mode - PCIe Endpoint mode (0 = 1x16, 2x8, ..., see card_conf.tcl for card-specific options)
# 4. arch - PCIe Module architecture (USP, P-TILE, R_TILE, ...)
proc dts_pcie_core_dbg {base endpoints mode arch} {
    set probes 2
    set probes_off [expr $probes*64]
    set events 16
    set event_off 0x10
    set event_names {ph_r0_7  ph_r8_31  ph_r32_127  ph_r128_255   \
                     pd_r0_7  pd_r8_31  pd_r32_127  pd_r128_4095  \
                     nph_r0_7 nph_r8_31 nph_r32_127 nph_r128_255  \
                     npd_r0_7 npd_r8_31 npd_r32_127 npd_r128_4095 \
                    }
    set events_fifo_en 1
    set endpoints_off [expr $probes_off + $events*$event_off]
    set ret ""
    for {set ep 0} {$ep < $endpoints} {incr ep} {
        set ep_base [expr $base + $ep*$endpoints_off]
        set probe_name "pcie_core_debug_probe_$ep"
        append ret "streaming_debug_$ep:" [dts_streaming_debug $ep_base $probe_name $probes]
        # Endpoint 0 keeps the original names of the event counters, tools refer to them.
        set ep_sfx [expr {$ep > 0 ? "_$ep" : ""}]
        for {set ev 0} {$ev < $events} {incr ev} {
            set ec_base [expr $ep_base + $probes_off + $ev*$event_off]
            set ec_name "pcie_credits_event_counter_[lindex $event_names $ev]$ep_sfx"
            append ret "event${ep_sfx}_$ev:" [dts_event_counter $ec_base $ec_name $events_fifo_en]
        }
    }

    return $ret
}
