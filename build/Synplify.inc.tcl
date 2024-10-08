# Synplify.inc.tcl: Synplify global include Tcl script to compile whole design
# Copyright (C) 2023 BrnoLogic
# Author: Lukas Kekely <kekely@brnologic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

if {![info exists $env(OFM_PATH)]} {
    set OFM_PATH $env(OFM_PATH)
}

if {![info exists $env(FIRMWARE_BASE)]} {
    set FIRMWARE_BASE $env(FIRMWARE_BASE)
}

# Hack for older synth scripts: set OFM_PATH from FIRMWARE_BASE
# This hack is only for components inside OFM repository

if {![info exists OFM_PATH]} {
    set OFM_PATH $FIRMWARE_BASE
}

# Source scripts with further procedures utilized during design compilation
source $OFM_PATH/build/Shared.tcl
source $OFM_PATH/build/DevTree.tcl
source $OFM_PATH/build/targets.tcl

# -----------------------------------------------------------------------------
#                         Procedures and functions
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# Procedure AddInputFiles
# Recursively goes through the components hierarchy and adds all design files to project.
#
proc AddInputFiles {synth_flags hierarchy {eval_mod_proc "EvalFile"} {eval_comp_proc "EvalComp"}} {
    # Define auxiliary variables
    upvar 1 $hierarchy HIERARCHY
    upvar 1 $synth_flags SYNTH_FLAGS

    set FILES [list ]
    set SV_LIBS [list ]

    # Add packages
    PrintLabel "Packages compilation"

    ApplyToMods $HIERARCHY(PACKAGES) $eval_mod_proc FILES

    # Add components
    PrintLabel "Components compilation"
    ApplyToComponents $HIERARCHY(COMPONENTS) $eval_mod_proc FILES SV_LIBS 1 $eval_comp_proc

    # Add modules
    PrintLabel "Modules compilation"
    ApplyToMods $HIERARCHY(MOD) $eval_mod_proc FILES
    ApplyToMods $HIERARCHY(TOP_LEVEL) $eval_mod_proc FILES

    # Add constraints
    PrintLabel "Constraints compilation"
    ApplyToMods $SYNTH_FLAGS(CONSTR) $eval_mod_proc FILES

    return $FILES
}

# -----------------------------------------------------------------------------
# Procedure EvalFile
# Add file to the project
#
proc EvalFile {FNAME OPT} {
    set opt(LIBRARY) "work"
    array set opt $OPT

    lappend LIB_PARAM
    lappend LIB_PARAM -lib $opt(LIBRARY)

    set FEXT [file extension $FNAME]

    if {$opt(TYPE) == ""} {
        if { $FEXT == ".vhd" } {
            # VHDL file
            add_file -vhdl {*}$LIB_PARAM $FNAME
            puts "INFO: Library $opt(LIBRARY): File added: $FNAME"
        } elseif { $FEXT == ".v" } {
            # Verilog file
            add_file -verilog {*}$LIB_PARAM $FNAME
            puts "INFO: Library $opt(LIBRARY): File added: $FNAME"
        } elseif { $FEXT == ".sdc" } {
            # Constraints
            add_file -constraint $FNAME
            puts "INFO: General constraints: File added: $FNAME"
        } else {
            # Not yet supported file type
            puts "WARNING: Adding $FEXT files to the project is not yet supported."
            puts "WARNING: File was not added: $FNAME!"
        }
    } else {
        # Not yet supported option
        puts "WARNING: Using $opt(TYPE) file type in the project is not yet supported."
        puts "WARNING: File was not added: $FNAME!"
    }
}

# Perform specified action at the beginning of component's processing.
proc EvalComp {ENTITY ENTITY_BASE ARCHGRP} {
    set ENTITY_VFILE "$ENTITY_BASE/Synplify_presynth.tcl"

    if {[file exists $ENTITY_VFILE]} {
        source $ENTITY_VFILE
    }
}

# -----------------------------------------------------------------------------
# Procedure SetupDesign
# Creates a new project with the name defined in the SYNTH_FLAGS(OUTPUT)
# parameter. (If the project already exists, it is first removed and the new
# project is created instead.) For the new project, the procedure sets the type
# of FPGA and the name of output files.
#
proc SetupDesign {synth_flags} {
    # HACK for toplevel TCL files which doesn't use nb_main
    global NB_MAIN_CALLED
    if {![info exist NB_MAIN_CALLED]} {
        set NB_MAIN_CALLED 1
        nb_main
    }

    # Define auxiliary variables corresponding to selected SYNTH_FLAGS items.
    upvar 1 $synth_flags SYNTH_FLAGS

    puts "Using FPGA part: $SYNTH_FLAGS(DEVICE) - $SYNTH_FLAGS(FPGA)"
    puts "Using project name: $SYNTH_FLAGS(OUTPUT)"

    # Create and open a new project with name specified by variable OUTPUT
    project -new "$SYNTH_FLAGS(OUTPUT).prj"
    set_option -reporting_filename "$SYNTH_FLAGS(OUTPUT).ta"
    project -result_file "$SYNTH_FLAGS(OUTPUT).edf"

    # Common project options
    impl -add synth1 -type fpga
    impl -active "synth1"
    set_option -project_relative_includes 1
    set_option -use_vivado 0

    # Target technology and FPGA
    set_option -technology $SYNTH_FLAGS(DEVICE)
    set_option -part $SYNTH_FLAGS(FPGA)
    set_option -package $SYNTH_FLAGS(FPGA)
    set_option -speed_grade -1
    set_option -part_companion ""

    # Define VHDL-2008 as default dialect for VHDL input files
    set_option -vhdl2008 1

    # Apply user settings
    foreach i $SYNTH_FLAGS(SETUP_FLAGS) {
        # TODO: Implement when needed
    }
}

# -----------------------------------------------------------------------------
# Procedure AddInputFiles
# Recursively goes through the components hierarchy and adds all design files to project.
#
proc AddInputFiles {synth_flags hierarchy {eval_mod_proc "EvalFile"} {eval_comp_proc "EvalComp"}} {
    # Define auxiliary variables
    upvar 1 $hierarchy HIERARCHY
    upvar 1 $synth_flags SYNTH_FLAGS

    set FILES [list ]
    set SV_LIBS [list ]

    # Add packages
    PrintLabel "Packages compilation"

    ApplyToMods $HIERARCHY(PACKAGES) $eval_mod_proc FILES

    # Add components
    PrintLabel "Components compilation"
    ApplyToComponents $HIERARCHY(COMPONENTS) $eval_mod_proc FILES SV_LIBS 1 $eval_comp_proc

    # Add modules
    PrintLabel "Modules compilation"
    ApplyToMods $HIERARCHY(MOD) $eval_mod_proc FILES
    ApplyToMods $HIERARCHY(TOP_LEVEL) $eval_mod_proc FILES

    # Add constraints
    PrintLabel "Constraints compilation"
    ApplyToMods $SYNTH_FLAGS(CONSTR) $eval_mod_proc FILES

    return $FILES
}

# -----------------------------------------------------------------------------
# Procedure SynthesizeDesign
# Sets synthesis properties, runs synthesis and reports timing/utilization
# after synthesis.
#
proc SynthesizeDesign {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    SynthesizeDesignSetup SYNTH_FLAGS
    # Skip actual implementation if one of the variables is set to 1/true
    if {$SYNTH_FLAGS(PROJ_ONLY)} {return}
    SynthesizeDesignRun SYNTH_FLAGS
}

proc SynthesizeDesignSetup {synth_flags} {

    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Synthesis Properties Setting"

    # Define top level module (if defined)
    if { [info exist SYNTH_FLAGS(MODULE)] } {
        set_option -top_module $SYNTH_FLAGS(MODULE)
    }

    project -save "$SYNTH_FLAGS(OUTPUT).prj"
}

proc SynthesizeDesignRun {synth_flags} {
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Synthesize"
    project -run
    file copy -force synth1/$SYNTH_FLAGS(OUTPUT).edf ./$SYNTH_FLAGS(OUTPUT).edf
}



proc nb_sanitize_vars {synth_flags hierarchy} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS
    upvar 1 $hierarchy HIERARCHY

    # Create empty lists
    lappend HIERARCHY(PACKAGES)
    lappend HIERARCHY(COMPONENTS)
    lappend HIERARCHY(MOD)
    lappend HIERARCHY(TOP_LEVEL)

    lappend SYNTH_FLAGS(SETUP_FLAGS)
    lappend SYNTH_FLAGS(USER_GENERICS)
    lappend SYNTH_FLAGS(CONSTR)
    lappend SYNTH_FLAGS(NFW_FILES)

    set SYNTH_FLAGS(TOOL) "synplify"

    # Set default values
    if {![info exists SYNTH_FLAGS(PROJ_ONLY)]} {
        set SYNTH_FLAGS(PROJ_ONLY) false
    }
}

nb_sanitize_vars SYNTH_FLAGS HIERARCHY
