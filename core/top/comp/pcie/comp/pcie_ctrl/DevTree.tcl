# 1. base - base address on MI bus
# 2. endpoints - number of PCIe endpoints
# 3. mode - PCIe Endpoint mode (0 = 1x16, 2x8, ..., see card_conf.tcl for card-specific options)
# 4. arch - PCIe Module architecture (USP, P-TILE, R_TILE, ...)
proc dts_pcie_ctrl_dbg {base endpoints mode arch} {
    set probes 1
    set probes_off [expr $probes*64]
    set dma_ports_per_ep 1
    if {$mode == 0 && ($arch == "P_TILE" || $arch == "R_TILE")} {set dma_ports_per_ep [expr 2*$endpoints]}
    set ret ""
    for {set ep 0} {$ep < $endpoints} {incr ep} {
        for {set dp 0} {$dp < $dma_ports_per_ep} {incr dp} {
            append ret "stream_dbg_ep${ep}_dmaport${dp}:" [dts_streaming_debug [expr $base + ($ep*$dma_ports_per_ep+$dp)*$probes_off] "pcie_ctrl_debug_probe_ep${ep}_dmaport${dp}" $probes]
        }
    }

    return $ret
}
