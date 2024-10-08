# Vivado.inc.tcl: Vivado global include tcl script to compile all design
# Copyright (C) 2013 CESNET
# Author: Viktor Puš <pus@cesnet.cz>
#         Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

# Including filtering procedures
source $OFM_PATH/build/scripts/vivado/msg_filter/tcl_msg_filters.tcl

# ---------------------------------------------------------------------
#                     Procedures and functions
# ---------------------------------------------------------------------

# -----------------------------------------------------------------------------
# Procedure EvalFile
# Add file to the project
#
proc EvalFile {FNAME OPT} {
    set opt(LIBRARY) "work"
    array set opt $OPT

    set FEXT [file extension $FNAME]

    if {$opt(TYPE) == ""} {
        add_files -norecurse $FNAME
        if {$opt(LIBRARY) != "work"} {
            set_property LIBRARY $opt(LIBRARY) [get_files $FNAME]
        }
        set vhdlfiles [get_files -quiet -filter {FILE_TYPE == VHDL} $FNAME]
        if {$vhdlfiles ne ""} {set_property FILE_TYPE {VHDL 2008} $vhdlfiles}
        puts "Library $opt(LIBRARY): File added: $FNAME"
    } elseif {$opt(TYPE) == "CONSTR_VIVADO"} {
        puts "Constraints file added: $FNAME"
        add_files -fileset constrs_1 -norecurse $FNAME

        if {[info exists opt(SCOPED_TO_REF)]} {
            puts "- file scoped to ref: $opt(SCOPED_TO_REF)"
            set_property SCOPED_TO_REF $opt(SCOPED_TO_REF) [get_files [file tail $FNAME]]
        }
        if {[info exists opt(PROCESSING_ORDER)]} {
            puts "- file processing order: $opt(PROCESSING_ORDER)"
            set_property PROCESSING_ORDER $opt(PROCESSING_ORDER) [get_files [file tail $FNAME]]
        }
        if {[info exists opt(USED_IN)]} {
            puts "- file used in: $opt(USED_IN)"
            set_property USED_IN $opt(USED_IN) [get_files [file tail $FNAME]]
        }
    } elseif {$opt(TYPE) == "VIVADO_IP_XACT"} {
        add_files -norecurse $FNAME
        puts "IP added: $FNAME"
    } elseif {$opt(TYPE) == "VIVADO_BD"} {
        add_files -norecurse $FNAME
        puts "BD added: $FNAME"
        generate_target all [get_files $FNAME] -force
        upgrade_ip [get_ips *] -quiet
    } elseif {$opt(TYPE) == "VIVADO_TCL"} {
        if {[info exists opt(PHASE)] && "ADD_FILES" in $opt(PHASE)} {
            puts "Running script: $FNAME"

            set vars ""
            if {[info exists opt(VARS)]} {
                set vars $opt(VARS)
            }
            source_with_vars $FNAME $vars
        }
    }


    foreach {param_name param_value} $OPT {
        if {$param_name == "VIVADO_SET_PROPERTY"} {
            puts "- file set_propery params: $param_value"
            set_property {*}$param_value [get_files [file tail $FNAME]]
        }
    }
}

# Call component's local Vivado_presynth.tcl
# (used for local constraints application before synthesis)
proc EvalComp {ENTITY ENTITY_BASE ARCHGRP} {
    # Vivado_presynth: DEPRECATED
    set ENTITY_VFILE "$ENTITY_BASE/Vivado_presynth.tcl"

    if {[file exists $ENTITY_VFILE]} {
        source $ENTITY_VFILE
    }
}

# ---------------------------------------------------------------------
# Procedure SetupDesign - creates a new project with the name defined in MODULE
# parameter. If the project already exists, it removes the project including
# all its implementations. It sets the type of FPGA chip, for the synthesis is
# performed and finaly it sets the name of the output edif file defined in
# OUTPUT parameter.
#
proc SetupDesign {synth_flags} {
    # HACK for toplevel TCL files which doesn't use nb_main
    global NB_MAIN_CALLED
    if {![info exist NB_MAIN_CALLED]} {
        set NB_MAIN_CALLED 1
        nb_main
    }

    upvar 1 $synth_flags SYNTH_FLAGS

    puts "Using FPGA part: $SYNTH_FLAGS(FPGA)"

    # Create and open a new project with name specified by variable OUTPUT
    create_project -part $SYNTH_FLAGS(FPGA) -force $SYNTH_FLAGS(OUTPUT)

    # Define default target language
    set_param project.enableVHDL2008 1
    set_property target_language VHDL [current_project]
    set_property enable_vhdl_2008 1 [current_project]

    # Manual compile order (automatic is buggy in Vivado)
    set_property source_mgmt_mode DisplayOnly [current_project]

    set_param messaging.defaultLimit 3000

    # Apply user settings
    foreach i $SYNTH_FLAGS(SETUP_FLAGS) {
        if { $i == "USE_XPM_LIBRARIES" } {
            set_property XPM_LIBRARIES {XPM_CDC XPM_MEMORY XPM_FIFO} [current_project]
        } elseif { $i == "COMPILE_ORDER_AUTO" } {
            set_property source_mgmt_mode All [current_project]
        }
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
    ApplyToMods $SYNTH_FLAGS(CONSTR) $eval_mod_proc FILES "CONSTR_VIVADO"

    return $FILES
}

# -----------------------------------------------------------------------------
# Procedure SynthesizeDesign
# Sets synthesis properties, runs synthesis and reports timing/utilization
# after synthesis.
#
proc SynthetizeDesign {synth_flags} {
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
        set_property top $SYNTH_FLAGS(MODULE) [current_fileset]
    }

    # Set VHDL assert
    puts "VHDL assert enabled!"
    set_property -name {STEPS.SYNTH_DESIGN.ARGS.ASSERT} -value True -objects [get_runs synth_1]

    # VHDL standard settings (VHDL-2008 support, backward compatibility)
    if { [info exist SYNTH_FLAGS(VHDL2008)] } {
        puts "VHDL-2008 standard support set to: $SYNTH_FLAGS(VHDL2008)"
        if { !$SYNTH_FLAGS(VHDL2008) } {
            set_property FILE_TYPE {VHDL} [get_files -quiet -filter {FILE_TYPE == {VHDL 2008}}]
        }
    }

    # Set fanout limit
    if {[info exist SYNTH_FLAGS(FANOUT_LIMIT)] } {
        puts "Fanout limit set to: $SYNTH_FLAGS(FANOUT_LIMIT)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.FANOUT_LIMIT} \
            -value $SYNTH_FLAGS(FANOUT_LIMIT) -objects [get_runs synth_1]
    }

    # Set resource sharing
    if {[info exist SYNTH_FLAGS(RESOURCE_SHARING)] } {
        puts "Resource sharing set to: $SYNTH_FLAGS(RESOURCE_SHARING)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.RESOURCE_SHARING} \
            -value $SYNTH_FLAGS(RESOURCE_SHARING) -objects [get_runs synth_1]
    }

    # Set the number of BUFGs
    if {[info exist SYNTH_FLAGS(BUFG)] } {
        puts "The number of BUFGs set to: $SYNTH_FLAGS(BUFG)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.BUFG} \
            -value $SYNTH_FLAGS(BUFG) -objects [get_runs synth_1]
    }

    # Set synthesis directive
    if {[info exist SYNTH_FLAGS(SYNTH_DIRECTIVE)] } {
        puts "Synthesis directive set to: $SYNTH_FLAGS(SYNTH_DIRECTIVE)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.DIRECTIVE} \
            -value $SYNTH_FLAGS(SYNTH_DIRECTIVE) -objects [get_runs synth_1]
    }

    # Set LUT combining
    if {[info exist SYNTH_FLAGS(NO_LUT_COMBINE)] } {
        puts "LUT combining disabled: $SYNTH_FLAGS(NO_LUT_COMBINE)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.NO_LC} \
            -value $SYNTH_FLAGS(NO_LUT_COMBINE) -objects [get_runs synth_1]
    }

    # Set retiming
    if {[info exist SYNTH_FLAGS(RETIMING)] } {
        puts "Retiming enabled: $SYNTH_FLAGS(RETIMING)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.RETIMING} \
            -value $SYNTH_FLAGS(RETIMING) -objects [get_runs synth_1]
    }

    # Set rebuild
    if {[info exist SYNTH_FLAGS(FLATTEN_HIERARCHY)] } {
        puts "set flattening mode: $SYNTH_FLAGS(FLATTEN_HIERARCHY)"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY} \
            -value $SYNTH_FLAGS(FLATTEN_HIERARCHY) -objects [get_runs synth_1]
    }

    # Set build generics of toplevel entity
    if {[info exist SYNTH_FLAGS(USER_GENERICS)]} {
        set MOREOPT ""
        foreach g $SYNTH_FLAGS(USER_GENERICS) {
            append MOREOPT "-generic " [lindex $g 0] "=" [lindex $g 1] " "
        }
        puts "User-defined generics: $MOREOPT"
        set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} \
            -value $MOREOPT -objects [get_runs synth_1]
    }

    # Set Out-of-context mode
    if {[info exist SYNTH_FLAGS(OOC_MODE)]} {
        if {$SYNTH_FLAGS(OOC_MODE) == "1"} {
            set MOREOPT [get_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} \
                -object [get_runs synth_1]]
            append MOREOPT "-mode out_of_context "
            puts "Out-of-context mode set"
            set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} \
                -value $MOREOPT -objects [get_runs synth_1]
        }
    }

    # Set assertion severity level
    if {[info exist SYNTH_FLAGS(ASSERT_SEVERITY)]} {
        set_msg_config -id {Synth 8-63} -severity WARNING -new_severity $SYNTH_FLAGS(ASSERT_SEVERITY)
        puts "Assertion severity level set to: $SYNTH_FLAGS(ASSERT_SEVERITY)"
    } else {
        set_msg_config -id {Synth 8-63} -severity WARNING -new_severity ERROR
    }

    # Set severity of 'multi-driven net on pin ...'
    set_msg_config -id {Synth 8-6858} -severity WARNING -new_severity ERROR
    set_msg_config -id {Synth 8-6859} -severity WARNING -new_severity ERROR
    # Set severity of 'sensitivity list mistake'
    set_msg_config -id {Synth 8-614} -severity WARNING -new_severity ERROR

    if {$SYNTH_FLAGS(UPGRADE_IP)} {
        PrintLabel "Upgrading IP cores"
        foreach ip [get_ips] {
            upgrade_ip $ip
        }
    }
}

proc SynthesizeDesignRun {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Synthesize"
    launch_runs synth_1
    wait_on_run synth_1
    open_run synth_1

    PrintLabel "Report timing"
    set_delay_model -interconnect estimated
    report_timing_summary -delay_type min_max -report_unconstrained -check_timing_verbose -max_paths 10 -input_pins -name timing_1 -file $SYNTH_FLAGS(OUTPUT)_synth.tim

    PrintLabel "Report Utilization"
    report_utilization -file $SYNTH_FLAGS(OUTPUT)_synth.util

    # Load user DRC
    global OFM_PATH
    source $OFM_PATH/build/scripts/vivado/user_drc/load.tcl

    PrintLabel "Report DRC"
    report_drc -file $SYNTH_FLAGS(OUTPUT)_synth.drc

    # Write VHDL file for netlist simulation
    if {$SYNTH_FLAGS(WRITE_VHDL)} {
        write_vhdl -mode funcsim -force "$SYNTH_FLAGS(OUTPUT).vhd"
    }

    # Export to file
    if {[info exist SYNTH_FLAGS(WRITE_EDIF)] } {
        write_edif -force $SYNTH_FLAGS(OUTPUT)
    }
}

# -----------------------------------------------------------------------------
# Procedure ImplementDesign
# Sets implementation properties, runs implementation and reports
# timing/utilization after implementation.
#
proc ImplementDesign {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    ImplementDesignSetup SYNTH_FLAGS
    # Skip actual implementation if one of the variables is set to 1/true
    if {$SYNTH_FLAGS(PROJ_ONLY) || $SYNTH_FLAGS(SYNTH_ONLY)} {return}
    ImplementDesignRun SYNTH_FLAGS
}

proc ImplementDesignSetup {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Implementation Properties Setting"
    # Run script wbs_pre.tcl before writing the bitstream
    global OFM_PATH
    set_property STEPS.WRITE_BITSTREAM.TCL.PRE [file normalize $OFM_PATH/build/misc/vivado_wbs_pre.tcl] [get_runs impl_1]

    if {[info exist SYNTH_FLAGS(SOPT_DIRECTIVE)] } {
        puts "Implementation optimization directive set to: $SYNTH_FLAGS(SOPT_DIRECTIVE)"
        # opt_design (See Xilinx UG904)
        set_property -name {STEPS.OPT_DESIGN.ARGS.IS_ENABLED} \
            -value {true}        -objects [get_runs impl_1]
        set_property -name {STEPS.OPT_DESIGN.ARGS.VERBOSE}    \
            -value $SYNTH_FLAGS(SOPT_VERBOSE)   -objects [get_runs impl_1]
        set_property -name {STEPS.OPT_DESIGN.ARGS.DIRECTIVE}  \
            -value $SYNTH_FLAGS(SOPT_DIRECTIVE) -objects [get_runs impl_1]
    }

    # backward compatibility (run power_opt_design by default)
    if {![info exist SYNTH_FLAGS(POWER_OPT_DESIGN)] } {
        set SYNTH_FLAGS(POWER_OPT_DESIGN) true
    }

    # power_opt_design
    puts "Run Power Opt Design: $SYNTH_FLAGS(POWER_OPT_DESIGN)"
    set_property -name {STEPS.POWER_OPT_DESIGN.ARGS.IS_ENABLED} \
        -value $SYNTH_FLAGS(POWER_OPT_DESIGN) -objects [get_runs impl_1]
    set_property -name {STEPS.POWER_OPT_DESIGN.ARGS.MORE OPTIONS} \
        -value {-verbose} -objects [get_runs impl_1]

    if {[info exist SYNTH_FLAGS(PLACE_DIRECTIVE)] } {
        puts "Placer optimization directive set to: $SYNTH_FLAGS(PLACE_DIRECTIVE)"
        # place_design (See Xilinx UG904)
        set_property -name {STEPS.PLACE_DESIGN.ARGS.DIRECTIVE}    \
            -value $SYNTH_FLAGS(PLACE_DIRECTIVE) -objects [get_runs impl_1]
        set_property -name {STEPS.PLACE_DESIGN.ARGS.MORE OPTIONS} \
            -value {-verbose}              -objects [get_runs impl_1]
    }

    # backward compatibility (run post_place_power_opt_design by default)
    if {![info exist SYNTH_FLAGS(PPLACE_POWER_OPT_DESIGN)] } {
        set SYNTH_FLAGS(PPLACE_POWER_OPT_DESIGN) true
    }

    # post_place_power_opt_design
    # (currently commented out becase power_opt_design is already enabled before
    #  placement)
#    puts "Run Post-place Power Opt Design: $SYNTH_FLAGS(PPLACE_POWER_OPT_DESIGN)"
#    set_property -name {STEPS.POST_PLACE_POWER_OPT_DESIGN.ARGS.IS_ENABLED} \
#        -value $SYNTH_FLAGS(PPLACE_POWER_OPT_DESIGN) -objects [get_runs impl_1]
#    set_property -name {STEPS.POST_PLACE_POWER_OPT_DESIGN.ARGS.MORE OPTIONS} \
#        -value {-verbose} -objects [get_runs impl_1]

    if {[info exist SYNTH_FLAGS(PPLACE_PHYS_OPT_DIRECTIVE)] } {
        puts "Post-place physical optimization directive set to: $SYNTH_FLAGS(PPLACE_PHYS_OPT_DIRECTIVE)"
        # phys_opt_design (See Xilinx UG904)
        set_property -name {STEPS.PHYS_OPT_DESIGN.ARGS.IS_ENABLED}   \
            -value {true}              -objects [get_runs impl_1]
        set_property -name {STEPS.PHYS_OPT_DESIGN.ARGS.DIRECTIVE}    \
            -value $SYNTH_FLAGS(PPLACE_PHYS_OPT_DIRECTIVE) -objects [get_runs impl_1]
        set_property -name {STEPS.PHYS_OPT_DESIGN.ARGS.MORE OPTIONS} \
            -value {-verbose}          -objects [get_runs impl_1]
    }

    if {[info exist SYNTH_FLAGS(ROUTE_DIRECTIVE)] } {
        puts "Router optimization directive set to: $SYNTH_FLAGS(ROUTE_DIRECTIVE)"
        # route_design (See Xilinx UG904)
        set_property -name {STEPS.ROUTE_DESIGN.ARGS.DIRECTIVE}    \
            -value $SYNTH_FLAGS(ROUTE_DIRECTIVE)  -objects [get_runs impl_1]
        set_property -name {STEPS.ROUTE_DESIGN.ARGS.MORE OPTIONS} \
            -value {-verbose} -objects [get_runs impl_1]
    }

    if {[info exist SYNTH_FLAGS(PROUTE_PHYS_OPT_DIRECTIVE)] } {
        puts "Post-route physical optimization directive set to: $SYNTH_FLAGS(PROUTE_PHYS_OPT_DIRECTIVE)"
        # phys_opt_design (See Xilinx UG904)
        set_property -name {STEPS.POST_ROUTE_PHYS_OPT_DESIGN.ARGS.IS_ENABLED}   \
            -value {true}              -objects [get_runs impl_1]
        set_property -name {STEPS.POST_ROUTE_PHYS_OPT_DESIGN.ARGS.DIRECTIVE}    \
            -value $SYNTH_FLAGS(PROUTE_PHYS_OPT_DIRECTIVE) -objects [get_runs impl_1]
        set_property -name {STEPS.POST_ROUTE_PHYS_OPT_DESIGN.ARGS.MORE OPTIONS} \
            -value {-verbose}          -objects [get_runs impl_1]
    }

    # Incremental synthesis
    if {[info exist SYNTH_FLAGS(DCP)] } {
        puts "Incremental compile checkpoint: $SYNTH_FLAGS(DCP)"
        set_property incremental_checkpoint $SYNTH_FLAGS(DCP) [get_runs impl_1]
    }
}

proc ImplementDesignRun {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Implement"

    launch_runs impl_1
    wait_on_run impl_1
    open_run impl_1

    PrintLabel "Report Timing"
    set_delay_model -interconnect actual

    report_timing_summary -delay_type min_max -report_unconstrained -check_timing_verbose -max_paths 10 -input_pins -name timing_1 -file $SYNTH_FLAGS(OUTPUT)_par.tim

    PrintLabel "Report Utilization"
    report_utilization -file $SYNTH_FLAGS(OUTPUT)_par.util

    PrintLabel "Report Power"
    report_power -file $SYNTH_FLAGS(OUTPUT)_par.pow

    # Load user DRC
    global OFM_PATH
    source $OFM_PATH/build/scripts/vivado/user_drc/load.tcl

    PrintLabel "Report DRC"
    report_drc -file $SYNTH_FLAGS(OUTPUT)_par.drc

    if {[info exist SYNTH_FLAGS(DCP)] } {
        PrintLabel "Report Incremental Reuse"
        report_incremental_reuse -file $SYNTH_FLAGS(OUTPUT)_par.reuse
    }

    # Write checkpoint for future reuse
    write_checkpoint -force $SYNTH_FLAGS(OUTPUT).dcp
}

# ---------------------------------------------------------------------
# Procedure SaveDesign - saves current project implementation. It copies the
# output edif file to root project directory, where the Makefile expects this
# output edif file. OUTPUT parameter specifies the name of output edif file.
# Finally it closes the project.
#
proc SaveDesign {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    # Manually run the pre-write bitstream script
    PrintLabel "Run pre-write bitstream script"
    global OFM_PATH
    source $OFM_PATH/build/misc/vivado_wbs_pre.tcl

    PrintLabel "Write bitstream"
    set ROOTNAME [pwd]/$SYNTH_FLAGS(OUTPUT)
    write_bitstream -force $ROOTNAME.bit

    close_project

    # INFO: Create archive AFTER close_project - random issues with insufficient memory
    nb_nfw_archive_create SYNTH_FLAGS
}

proc nb_nfw_archive_create {synth_flags} {
    global env
    upvar 1 $synth_flags SYNTH_FLAGS

    # Create temporary directory
    file mkdir $env(NETCOPE_TEMP)build_save_design

    # List of target files to be copied
    lappend NFW_FILES

    # FIXME: Add output bitstream to .nfw archive
    lappend SYNTH_FLAGS(NFW_FILES) [list $SYNTH_FLAGS(OUTPUT).bit $SYNTH_FLAGS(FPGA).bit]

    # Copy each file from SYNTH_FLAGS(NFW_FILES) list to temporary directory
    foreach f $SYNTH_FLAGS(NFW_FILES) {
        file copy [lindex $f 0] $env(NETCOPE_TEMP)build_save_design/[lindex $f 1]
        lappend NFW_FILES [lindex $f 1]
    }

    # Run tar utility
    if {[catch {exec tar -czf $SYNTH_FLAGS(OUTPUT).nfw -C $env(NETCOPE_TEMP)build_save_design {*}$NFW_FILES} msg]} {
        puts stderr "Packaging the firmware file failed:\n$msg"
    }

    # Delete temporary directory
    file delete -force $env(NETCOPE_TEMP)build_save_design
}

# -----------------------------------------------------------------------------
# Procedure CheckTiming
#
proc CheckTiming {synth_flags} {
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Timing Check"

    set TREPORT $SYNTH_FLAGS(OUTPUT)_par.tim
    set fp [open $TREPORT]
    # Search the file for the sentence
    while {[gets $fp line] >= 0} {
        if {[regexp "Timing constraints are not met." $line]} {
            puts "Timing constraints were NOT met!"
            seek $fp 0
            # Search the file for TNS and WNS
            while {[gets $fp line] >= 0} {
                if {[regexp "WNS" $line]} {
                    gets $fp line
                    gets $fp line
                    set WNSTNS [regexp -all -inline {\S+} $line]
                    puts -nonewline "WNS = "
                    puts [lindex $WNSTNS 0]
                    puts -nonewline "TNS = "
                    puts [lindex $WNSTNS 1]
                    return -code error
                }
            }
            return -code error
        }
    }
    puts "All constraints were met."
}

# ---------------------------------------------------------------------
# Procedure SynthesizeProject - automaticly performs all previosly defined
# procedures. Alternatively to this function, user can manualy call
# previously defined procedures and use addition commands to customize
# synthesis process
#
proc SynthesizeProject {synth_flags hierarchy} {
    upvar 1 $synth_flags SYNTH_FLAGS
    upvar 1 $hierarchy HIERARCHY

    # synthesis setting
    SetupDesign SYNTH_FLAGS

    # add input files
    AddInputFiles SYNTH_FLAGS HIERARCHY

    # design synthesis
    SynthetizeDesign SYNTH_FLAGS

    # design implementation
    ImplementDesign SYNTH_FLAGS

    if {!$SYNTH_FLAGS(PROJ_ONLY) && !$SYNTH_FLAGS(SYNTH_ONLY)} {
        # Save implemented design
        if {$SYNTH_FLAGS(PHASE_SAVE)} {
            SaveDesign SYNTH_FLAGS
        }

        # Check design timing after implementation
        CheckTiming SYNTH_FLAGS

        # Filter Vivado messages
        PrintLabel "Filter Vivado Messages"
        filter_msg
    }
}


# -----------------------------------------------------------------------------
#                Procedures and functions for message filtering
# -----------------------------------------------------------------------------


# get_all_log_files
# This procedure parses all log files in the current directory and returns a
# unique list of paths to all log files utilized during the run of the Vivado.
# The list starts with names of the log files in the current directory and
# continues with paths to runme.log files utilized in different
# synthesis/implementation runs.
#
proc get_all_log_files {} {
    global env

    # filename of Vivado's main log
    set MAIN_LOGFILES $env(OUTPUT_NAME).log

    # construct a list of paths to all utilized log files
    set LOGFILES $MAIN_LOGFILES
    foreach LOGFILE $MAIN_LOGFILES {

        # open the current log file for reading
        set LOGFILE_HANDLE [open $LOGFILE "r"]

        # read the current log file and extract all references to runme.log files
        while { [gets $LOGFILE_HANDLE LINE] >= 0 } {
            # paths to runme.log files are in the vivado.tcl present on lines
            # starting with "Run output will be captured here: "
            if { [regexp "(^Run output will be captured here: )(.*)" $LINE -> MSG PATH] } {
                lappend LOGFILES $PATH
            }
        }
    }

    # return a list of unique paths
    return [lsort -unique $LOGFILES]
}


# -----------------------------------------------------------------------------
# get_all_msg_lines
# This procedure parses the given file and returns a list of all lines
# containing a message (lines starting with INFO, WARNING, CRITICAL WARNING or
# ERROR), which were extracted from the given file.
#
proc get_all_msg_lines { FILENAME } {

    # open the given file for reading
    set LOGFILE [open $FILENAME "r"]

    # extract all message lines into the MSG_LINES list
    set MSG_LINES [list ]
    while { [gets $LOGFILE LINE] >= 0 } {
        if { [regexp "^INFO" $LINE] } {
            lappend MSG_LINES $LINE
        } elseif { [regexp "^WARNING" $LINE] } {
            lappend MSG_LINES $LINE
        } elseif { [regexp "^CRITICAL WARNING" $LINE] } {
            lappend MSG_LINES $LINE
        } elseif { [regexp "^ERROR" $LINE] } {
            lappend MSG_LINES $LINE
        }
    }

    # return the list
    return $MSG_LINES
}

# -----------------------------------------------------------------------------
# isRealSynth: DEPRECATED
# Returns true if the Synthesis process is executed in this tcl session
#
proc isRealSynth { } {
    global env
    global SYNTH_FLAGS

    if {$SYNTH_FLAGS(PROJ_ONLY)} {
        return false
    }
    return true
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

    set SYNTH_FLAGS(TOOL) "vivado"

    if {[info commands version] != ""} {
        set SYNTH_FLAGS(TOOL_VERSION) [version -short]
    } else {
        regexp {Vivado v([0-9\.]+) } [exec vivado -version] void SYNTH_FLAGS(TOOL_VERSION)
    }

    # Set default values
    if {![info exists SYNTH_FLAGS(PROJ_ONLY)]} {
        set SYNTH_FLAGS(PROJ_ONLY) false
    }
    if {![info exists SYNTH_FLAGS(SYNTH_ONLY)]} {
        set SYNTH_FLAGS(SYNTH_ONLY) false
    }
    if {![info exists SYNTH_FLAGS(PHASE_SAVE)]} {
        set SYNTH_FLAGS(PHASE_SAVE) true
    }
    if {![info exist SYNTH_FLAGS(WRITE_VHDL)]} {
        set SYNTH_FLAGS(WRITE_VHDL) false
    }
    if {![info exist SYNTH_FLAGS(UPGRADE_IP)] } {
        set SYNTH_FLAGS(UPGRADE_IP) true
    }
    if {![info exist SYNTH_FLAGS(SOPT_VERBOSE)] } {
        set SYNTH_FLAGS(SOPT_VERBOSE) false
    }
}

nb_sanitize_vars SYNTH_FLAGS HIERARCHY
