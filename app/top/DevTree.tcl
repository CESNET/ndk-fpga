proc dts_application {base eth_streams mem_ports} {
    set mi_ports_raw [expr $eth_streams + $mem_ports * 2]

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
            append ret [dts_app_minimal_core $i $core_base $subaddr_w]
    }

    for {set i 0} {$i < $mem_ports} {incr i} {
            set mem_tester_base [expr $base + $subaddr_w * ($eth_streams + $i)]
            append ret "mem_tester_$i:" [mem_tester $mem_tester_base $i]
    }

    for {set i 0} {$i < $mem_ports} {incr i} {
        set mem_logger_base [expr $base + $subaddr_w * ($eth_streams + $mem_ports + $i)]
        append ret "mem_logger_$i:" [data_logger $mem_logger_base $i "mem_logger"]
    }

    set multicore_debug_base [expr $base]
    append ret [dts_multicore_debug_core 0 $multicore_debug_base $subaddr_w]

	append ret "};"
	return $ret
}

proc dts_app_minimal_core {index base reg_size} {
    global ETH_PORT_CHAN

	set ret ""
	append ret "app_core_minimal_$index {"
	append ret "reg = <$base $reg_size>;"
    append ret "compatible = \"cesnet,minimal,app_core\";"
    append ret [dts_mvb_channel_router "rx_chan_router" $base $ETH_PORT_CHAN($index)]
    append ret "};"
	return $ret
}

proc dts_multicore_debug_core {index base reg_size} {
	set ret ""
	append ret "multicore_debug_core$index {"
    append ret "compatible = \"ziti,minimal,multicore_debug_core\";"
	append ret "reg = <$base $reg_size>;"
    append ret "};"
	return $ret
}

proc dts_build_project {} {
	return [dts_build_netcope]
}
