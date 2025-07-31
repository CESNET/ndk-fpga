# 1. base - base address on MI bus
# 2. endpoints - number of PCIe endpoints
# 3. mode - PCIe Endpoint mode (0 = 1x16, 2x8, ..., see card_conf.tcl for card-specific options)
# 4. arch - PCIe Module architecture (USP, P-TILE, R_TILE, ...)
proc dts_pcie_ctrl_dbg {base endpoints mode arch} {
    set probes 4
    set probes_off 0x200
    set probes_ptc 6
    set dma_ports_per_ep 1
    set pcie_ep_off 0x1000
    if {($mode == 0 && $arch == "P_TILE") || ($mode == 1 && $arch == "R_TILE")} {set dma_ports_per_ep [expr 2*$endpoints]}
    if {($mode == 0 && $arch == "R_TILE")} {set dma_ports_per_ep [expr 4*$endpoints]}
    set ret ""
    for {set ep 0} {$ep < $endpoints} {incr ep} {
        for {set dp 0} {$dp < $dma_ports_per_ep} {incr dp} {
            append ret "stream_dbg_ep${ep}_dmaport${dp}:" [dts_streaming_debug [expr $base + ($ep*$pcie_ep_off) + ($dp*$probes_off)] "pcie_ctrl_debug_probe_ep${ep}_dmaport${dp}" $probes]
        }
        append ret [dts_event_counter [expr $base + ($ep*$pcie_ep_off) + ($dma_ports_per_ep*$probes_off) + 0x00] "eve_pcie_tags_0_$ep" 1]
        append ret [dts_event_counter [expr $base + ($ep*$pcie_ep_off) + ($dma_ports_per_ep*$probes_off) + 0x10] "eve_pcie_tags_1to31_$ep" 1]
        append ret [dts_event_counter [expr $base + ($ep*$pcie_ep_off) + ($dma_ports_per_ep*$probes_off) + 0x20] "eve_pcie_tags_32to127_$ep" 1]
        append ret [dts_event_counter [expr $base + ($ep*$pcie_ep_off) + ($dma_ports_per_ep*$probes_off) + 0x30] "eve_pcie_tags_128plus_$ep" 1]

        append ret "stream_dbg_ep${ep}_ptc:" [dts_streaming_debug [expr $base + ($ep*$pcie_ep_off) + (($dma_ports_per_ep + 1)*$probes_off)] "pcie_ctrl_debug_probe_ep${ep}_ptc" $probes_ptc]
    }

    return $ret
}
