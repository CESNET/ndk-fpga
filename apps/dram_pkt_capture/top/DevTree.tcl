proc dts_application {base generics} {
    array set GENERICS $generics

    set eth_streams $GENERICS(ETH_STREAMS)

    # One MI port per ETH stream (MI_PORTS in application_core.vhd)
    set mi_ports_raw $eth_streams
    # Round to nearest power of 2
    set mi_ports 1
    while {$mi_ports < $mi_ports_raw} {
        set mi_ports [expr {$mi_ports * 2}]
    }
    set subaddr_w [expr 0x02000000 / $mi_ports]

    set ret ""
    append ret "application {"

    for {set i 0} {$i < $eth_streams} {incr i} {
        set core_base [expr $base + $subaddr_w*$i]
        append ret [dts_app_dram_pkt_capture_core $i $core_base $subaddr_w]
    }

    append ret "};"
    return $ret
}

proc dts_app_dram_pkt_capture_core {index base reg_size} {
    global ETH_PORT_CHAN

    set ret ""
    append ret "app_core_dram_pkt_capture_$index {"
    append ret "reg = <$base $reg_size>;"
    append ret "compatible = \"cesnet,dram_pkt_capture,app_core\";"
    append ret [dts_mvb_channel_router "rx_chan_router" $base $ETH_PORT_CHAN($index) 2 1]
    append ret "    rx_speed_meter {"
    append ret "        compatible = \"cesnet,ofm,speed_meter\";"
    append ret "        reg = <0x[format %x [expr $base + 0x1000]] 0x1000>;"
    append ret "    };"
    append ret "    "
    append ret "    tx_speed_meter {"
    append ret "        compatible = \"cesnet,ofm,speed_meter\";"
    append ret "        reg = <0x[format %x [expr $base + 0x2000]] 0x1000>;"
    append ret "    };"
    append ret "    stream_dbg_$index:" [dts_streaming_debug [expr $base + 0x3000] "app_core_debug_$index" 3]
    append ret "    app_status {"
    append ret "        compatible = \"cesnet,dram_pkt_capture,app_status\";"
    append ret "        reg = <0x[format %x [expr $base + 0x4000]] 0x1000>;"
    append ret "    };"
    append ret "};"
    return $ret
}

proc dts_build_project {} {
    return [dts_build_netcope]
}
