proc dts_application {base generics} {
    array set GENERICS $generics

    set eth_streams $GENERICS(ETH_STREAMS)
    set ddr_ports $GENERICS(DDR_PORTS)
    set hbm_ports $GENERICS(HBM_PORTS)

    # ETH streams + 1 port for DDR/HBM testers
    set mi_ports_raw [expr $eth_streams + 1]
    # Round to nearest power of 2
    set mi_ports 1
    while {$mi_ports < $mi_ports_raw} {
        set mi_ports [expr {$mi_ports * 2}]
    }
    set subaddr_w [expr 0x02000000 / $mi_ports]

    # 2x DDR ports + 1 HBM tester port
    set mt_mi_ports_raw [expr 2 * $ddr_ports + 1]
    # Round to nearest power of 2
    set mt_mi_ports 1
    while {$mt_mi_ports < $mt_mi_ports_raw} {
        set mt_mi_ports [expr {$mt_mi_ports * 2}]
    }
    set mt_subaddr_w [expr 0x200000 / $mt_mi_ports]

    set ret ""
    append ret "application {"

    for {set i 0} {$i < $eth_streams} {incr i} {
        set core_base [expr $base + $subaddr_w*$i]
        append ret [dts_app_minimal_core $i $core_base $subaddr_w]
    }

    for {set i 0} {$i < $ddr_ports} {incr i} {
        set mem_tester_base [expr $base + $subaddr_w * $eth_streams + $mt_subaddr_w * $i]
        append ret "ddr_tester_$i:" [mem_tester $mem_tester_base $i]
    }

    for {set i 0} {$i < $ddr_ports} {incr i} {
        set mem_logger_base [expr $base + $subaddr_w * $eth_streams + $mt_subaddr_w * ($ddr_ports + $i)]
        append ret "ddr_logger_$i:" [data_logger $mem_logger_base $i "mem_logger"]
    }

    if {$hbm_ports > 0} {
        set hbm_tester_base [expr $base + $subaddr_w * $eth_streams + $mt_subaddr_w * (2 * $ddr_ports)]
        append ret [dts_hbm_tester "hbm_tester" $hbm_tester_base]
    }

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

proc dts_build_project {} {
    return [dts_build_netcope]
}
