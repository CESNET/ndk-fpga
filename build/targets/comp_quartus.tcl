# Quartus.tcl: Quartus script to compile specified module
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Run global Vivado Tcl script to include general functions
set OFM_PATH $env(OFM_PATH)
source $OFM_PATH/build/Quartus.inc.tcl

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

set CONSTR_FILENAME $env(NETCOPE_TEMP)Quartus.sdc

# Constraints settings
set SYNTH_FLAGS(CONSTR) "$CONSTR_FILENAME"

# Enable virtual pins
set SYNTH_FLAGS(VIRTUAL_PINS) 1
set SYNTH_FLAGS(SYNTH_ONLY) [expr {!([info exists env(IMPLEMENT)] && $env(IMPLEMENT))}]

# Define hierarchy variables
set HIERARCHY(PACKAGES)   ""
set HIERARCHY(COMPONENTS) [list [list $TOP_LEVEL_ENT $TOP_LEVEL_PATH $TOP_LEVEL_ARCHGRP]]
set HIERARCHY(MOD)        ""

###############################################################################
# Source Vivado.tcl script in entity synth directory if exists
# and allow user to modify some values
if {[file exists Quartus.inc.tcl]} {
    source Quartus.inc.tcl
}

# Select FPGA by DEVICE
if {![info exists SYNTH_FLAGS(FPGA)]} {
    if {![info exists SYNTH_FLAGS(DEVICE)]} {
        set SYNTH_FLAGS(DEVICE) "STRATIX10"
    }
    set SYNTH_FLAGS(FPGA) [string map {
            "STRATIX10"     "1SD280PT2F55E1VG"
            "AGILEX"        "AGIB027R29A1E2VR0"
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

    # Prepare design for synthesis
    SetupDesign   SYNTH_FLAGS
    AddInputFiles SYNTH_FLAGS HIERARCHY

    # Synthesize design
    SynthesizeDesign SYNTH_FLAGS
    ImplementDesign SYNTH_FLAGS
}

nb_main
