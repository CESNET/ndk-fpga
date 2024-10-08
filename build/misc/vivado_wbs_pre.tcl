## Remove unloced ports the design

global SYNTH_FLAGS
foreach i [get_ports -filter { IS_LOC_FIXED == "FALSE" }] {
    puts "Removing unloced port $i"
    disconnect_net -prune -objects $i
    if { [info exists SYNTH_FLAGS(TOOL_VERSION)] && $SYNTH_FLAGS(TOOL_VERSION) == "2019.1" } {
        remove_port $i
    }
}

foreach i [get_cells -filter {IS_LOC_FIXED == "FALSE" && REF_NAME == "OBUFT"}] {
	puts "Removing unloced OBUFT $i"
	remove_cell $i
}
