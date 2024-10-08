# comp_vivado.tcl: Target Tcl script for Vivado to compile single component
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Run global Vivado Tcl script to include general functions
set OFM_PATH $env(OFM_PATH)
source $OFM_PATH/build/Vivado.inc.tcl

# Specify top level entity & architecture
set TOP_LEVEL_ENT $env(TOP_LEVEL_ENT)
set TOP_LEVEL_ARCHGRP $env(TOP_LEVEL_ARCHGRP)
set TOP_LEVEL_PATH $env(TOP_LEVEL_PATH)

# Default period for CLK
set CLK_PORTS "CLK"
set CLK_PERIOD 5.0

# Override values from shell
if {[info exists env(TOP_LEVEL_ARCHGRP)]} {
    set TOP_LEVEL_ARCHGRP $env(TOP_LEVEL_ARCHGRP)
}
if {[info exists env(TOP_LEVEL_PATH)]} {
    set TOP_LEVEL_PATH $env(TOP_LEVEL_PATH)
}

if {[info exists env(CLK_PERIOD)]} {
    set CLK_PERIOD $env(CLK_PERIOD)
}

if {[info exists env(CLK_PORTS)]} {
    set CLK_PORTS $env(CLK_PORTS)
}

if {[info exists env(DEVICE)]} {
    set SYNTH_FLAGS(DEVICE) $env(DEVICE)
}

# Synthesis variables
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) $env(OUTPUT_NAME)

set CONSTR_FILENAME $env(NETCOPE_TEMP)Vivado.xdc

# Constraints settings
set SYNTH_FLAGS(CONSTR) "$CONSTR_FILENAME"

# Create Vivado project only
set SYNTH_FLAGS(PROJ_ONLY) false
set SYNTH_FLAGS(SYNTH_ONLY) [expr {!([info exists env(IMPLEMENT)] && $env(IMPLEMENT))}]
set SYNTH_FLAGS(PHASE_SAVE) false

# Enable "out of context" mode to turn off I/O buffers
set SYNTH_FLAGS(OOC_MODE) "1"

# Hierarchy setting
set HIERARCHY(PACKAGES)   ""
set HIERARCHY(MOD)        ""
set HIERARCHY(COMPONENTS) [list [list $TOP_LEVEL_ENT $TOP_LEVEL_PATH $TOP_LEVEL_ARCHGRP]]

###############################################################################
# Source Vivado.tcl script in entity synth directory if exists
# and allow user to modify some values
if {[file exists Vivado.inc.tcl]} {
    source Vivado.inc.tcl
}

# Select FPGA by DEVICE
if {![info exists SYNTH_FLAGS(FPGA)]} {
    if {![info exists SYNTH_FLAGS(DEVICE)]} {
        set SYNTH_FLAGS(DEVICE) "ULTRASCALE"
    }
    set SYNTH_FLAGS(FPGA) [string map {
            "VIRTEX7"       "xc7vh580thcg1931-2"
            "ULTRASCALE"    "xcvu7p-flvb2104-2-i"
        } $SYNTH_FLAGS(DEVICE)]
}

# Check if user modified some known variables
if {![info exists CONSTR_TEXT]} {
    set CONSTR_TEXT ""
    while {[llength $CLK_PERIOD] < [llength $CLK_PORTS]} {
        lappend CLK_PERIOD [expr [lindex $CLK_PERIOD end] + 1]
    }
    foreach CLK $CLK_PORTS CLK_P $CLK_PERIOD {
        append CONSTR_TEXT "create_clock -period $CLK_P \[get_ports $CLK\]\n"
    }
}

# Prepend info for which FPGA was constraint file generated
set CONSTR_TEXT "# Generated for $SYNTH_FLAGS(FPGA)\n$CONSTR_TEXT"

# Generate constraints file
nb_file_update $CONSTR_FILENAME $CONSTR_TEXT

proc target_default {} {
    global SYNTH_FLAGS HIERARCHY
    SynthesizeProject SYNTH_FLAGS HIERARCHY
}

nb_main
