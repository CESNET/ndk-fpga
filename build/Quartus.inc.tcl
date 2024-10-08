# Quartus.inc.tcl: Quartus global include Tcl script to compile whole design
# Copyright (C) 2017 CESNET
# Author: Jiri Matousek <matousek@cesnet.cz>
#         Jakub Cabal <cabal@cesnet.cz>
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
# Procedure qsys_script_ip_with_params
# Add or adjust existing tcl generated IP core in the project
#
proc qsys_script_with_params {script params} {
    set project_name [file dirname $script]/[string map {. _} [file rootname [file tail $script]]]
    set cmd "foreach {name value} {$params} { set \$name \$value }"
    exec find [file dirname $script] \( -name "*.qpf" -o -name "*.qsf" -o -name "DNI" -o -name "qdb" \) | xargs rm -rf
    exec qsys-script --new-quartus-project=$project_name --cmd=$cmd --script=$script 2>>qsys_log.txt
    exec find [file dirname $script] \( -name "*.qpf" -o -name "*.qsf" -o -name "DNI" -o -name "qdb" \) | xargs rm -rf
}

# -----------------------------------------------------------------------------
# Procedure EvalFile
# Add file to the project
#
proc EvalFile {FNAME OPT} {
    set opt(LIBRARY) "work"
    array set opt $OPT

    lappend LIB_PARAM
    if {$opt(LIBRARY) != "work"} {
        lappend LIB_PARAM "-library" $opt(LIBRARY)
    }

    set FEXT [file extension $FNAME]

    # Require Project package of Quartus Prime as required for the following commands
    package require ::quartus::project

    if {$opt(TYPE) == ""} {
        if { $FEXT == ".vhd" } {
            # VHDL file
            set_global_assignment -name VHDL_FILE $FNAME -hdl_version VHDL_2008 {*}$LIB_PARAM
            puts "INFO: Library $opt(LIBRARY): File added: $FNAME"
        } elseif { $FEXT == ".v" } {
            # Verilog file
            set_global_assignment -name VERILOG_FILE $FNAME {*}$LIB_PARAM
            puts "INFO: Library $opt(LIBRARY): File added: $FNAME"
        } elseif { $FEXT == ".sv" || $FEXT == ".svp" } {
            # System Verilog file
            set_global_assignment -name SYSTEMVERILOG_FILE $FNAME {*}$LIB_PARAM
            puts "INFO: Library $opt(LIBRARY): File added: $FNAME"
        } elseif { $FEXT == ".sdc" } {
            # SDC file
            set_global_assignment -name SDC_FILE $FNAME
            puts "INFO: Constraints file added: $FNAME"
        } elseif { $FEXT == ".qsys" } {
            # QSYS file
            set_global_assignment -name QSYS_FILE $FNAME
            puts "INFO: QSYS file added: $FNAME"
        } elseif { $FEXT == ".hex" } {
            # HEX file
            set_global_assignment -name HEX_FILE $FNAME
            puts "INFO: HEX file added: $FNAME"
        } elseif { $FEXT == ".qsf" } {
            # QSF file
            puts "INFO: Importing file to the project: $FNAME"
            source $FNAME
        } else {
            # Not yet supported file type
            puts "WARNING: Adding $FEXT files to the project is not yet supported."
            puts "WARNING: File was not added: $FNAME!"
        }
    } elseif {$opt(TYPE) == "CONSTR_QUARTUS"} {
        if {[info exists opt(SDC_ENTITY_FILE)]} {
            puts "- file assigned to instance: $opt(SDC_ENTITY_FILE)"
            set_instance_assignment -entity $opt(SDC_ENTITY_FILE) -name SDC_ENTITY_FILE $FNAME
        }
    } elseif {$opt(TYPE) == "PARTITION_QDB"} {
        if {[info exists opt(PARTITION_NAME)]} {
            puts "- partition $opt(PARTITION_NAME) assigned to instance: $opt(PARTITION_PATH)"
            set_instance_assignment -name PARTITION $opt(PARTITION_NAME) -to $opt(PARTITION_PATH)
            set_instance_assignment -name QDB_FILE_PARTITION $FNAME -to $opt(PARTITION_PATH)
        }
    } elseif {$opt(TYPE) == "SEARCH_PATH"} {
        puts "- set SEARCH_PATH for custom Quartus IP: $FNAME"
        set_global_assignment -name SEARCH_PATH $FNAME
    } elseif {$opt(TYPE) == "QUARTUS_IP" } {
        # IP file
        set_global_assignment -name IP_FILE $FNAME
        puts "INFO: IP file added: $FNAME"
    } elseif {$opt(TYPE) == "QUARTUS_TCL"} {
        if {[info exists opt(PHASE)] && "ADD_FILES" in $opt(PHASE)} {
            puts "Running script: $FNAME"

            set vars ""
            if {[info exists opt(VARS)]} {
                set vars $opt(VARS)
            }

            qsys_script_with_params $FNAME $vars

            if {"IP_TEMPLATE_GEN" in $opt(PHASE)} {
                set ip_build_dir [file normalize $opt(IP_BUILD_DIR)]
                foreach ipfile [glob -nocomplain *.ip] {
                    exec mv $ipfile $ip_build_dir
                    set_global_assignment -name IP_FILE "$ip_build_dir/$ipfile"
                    puts "INFO: IP file added: $ip_build_dir/$ipfile"
                }
            }
        }
    }
}

# Perform specified action at the beginning of component's processing.
proc EvalComp {ENTITY ENTITY_BASE ARCHGRP} {
    set ENTITY_VFILE "$ENTITY_BASE/Quartus_presynth.tcl"

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

    # Require Project package of Quartus Prime as required for the following commands
    package require ::quartus::project

    # Define auxiliary variables corresponding to selected SYNTH_FLAGS items.
    upvar 1 $synth_flags SYNTH_FLAGS

    puts "Using FPGA part: $SYNTH_FLAGS(FPGA)"
    puts "Using project name: $SYNTH_FLAGS(OUTPUT)"

    # Create and open a new project with name specified by variable OUTPUT
    project_new $SYNTH_FLAGS(OUTPUT) -overwrite -part $SYNTH_FLAGS(FPGA)

    # Define VHDL-2008 as default dialect for VHDL input files
    set_global_assignment -name VHDL_INPUT_VERSION VHDL_2008

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
# Procedure CreatePartition
# Create partition, works only after synthesis.
#
proc CreatePartition {synth_flags PARTITION_NAME PARTITION_HIERARCHICAL_PATH} {
    # Make environment variable accessible through "env" name.
    global env

    if {[info exist env(QUARTUS_FILELIST_ONLY)]} {
        # Environment variable was set, skip the rest of procedure
        puts "skip"
        return
    }

    # Require Project package of Quartus Prime as required for the following command
    package require ::quartus::project

    # Define partition
    set_instance_assignment -name PARTITION $PARTITION_NAME -to $PARTITION_HIERARCHICAL_PATH
    puts "Created $PARTITION_NAME partition."
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
    # Require Project and Flow packages of Quartus Prime as required for the
    # following commands
    package require ::quartus::project
    package require ::quartus::flow

    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Synthesis Properties Setting"

    # Define top level module (if defined)
    if { [info exist SYNTH_FLAGS(MODULE)] } {
        set_global_assignment -name TOP_LEVEL_ENTITY $SYNTH_FLAGS(MODULE)
    }

    # Enable VHDL assert
    if {$SYNTH_FLAGS(ASSERT_OFF)} {
        puts "VHDL assert disabled!"
    } else {
        puts "VHDL assert enabled!"
        set_global_assignment -name ENABLE_VHDL_STATIC_ASSERTIONS ON
    }

    # Set virtual pins
    if {$SYNTH_FLAGS(VIRTUAL_PINS)} {
        puts "All pins set to virtual mode."
        set_instance_assignment -name VIRTUAL_PIN ON -to *
    }

    # Automatic clear old IP files before IP Generation
    if { [info exist SYNTH_FLAGS(IP_FILES_CLEAN_ENABLE)] } {
        PrintLabel "Clearing old IP files..."
        execute_module -tool ipg -args "--clear_ip_generation_dirs"
    } else {
        puts "Automatic clearing of old IP files is DISABLED!"
    }

    PrintLabel "IP Generation"
    execute_module -tool ipg

    # Perform user bash script after IP cores generation
    if { [info exist SYNTH_FLAGS(SCRIPT_AFTER_IP_GEN)] } {
        global FIRMWARE_BASE
        puts "Perform user bash script after IP cores generation."
        # Script has $FIRMWARE_BASE variable as first argument.
        exec $SYNTH_FLAGS(SCRIPT_AFTER_IP_GEN) $FIRMWARE_BASE
    }

    # Quartus TLG stage, only for Quartus Prime Pro 21.2 and newer
    if { [info exist SYNTH_FLAGS(QUARTUS_TLG)] } {
        PrintLabel "Support-Logic Generation"
        qexec "quartus_tlg $SYNTH_FLAGS(OUTPUT)"
    }
}

proc SynthesizeDesignRun {synth_flags} {
    PrintLabel "Synthesize"

    execute_module -tool syn
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
}

proc ImplementDesignRun {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    PrintLabel "Implement"

    # Require Flow package of Quartus Prime as required for the following commands
    package require ::quartus::flow

    execute_module -tool fit

    PrintLabel "Report Timing"
    execute_module -tool sta

    PrintLabel "Report Power"
    execute_module -tool pow
}

# -----------------------------------------------------------------------------
# Procedure SaveDesign
# Generates a programming image and closes the current project.
#
proc SaveDesign {synth_flags} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS

    # Require Project and Flow packages of Quartus Prime as required for the following commands
    package require ::quartus::project
    package require ::quartus::flow

    PrintLabel "Save & Close"

    # Generate programming image
    execute_module -tool asm

    # Close project
    project_close

    # Convert programming image to RBF format
    if { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "RBF"} {
        nb_convert_to_rbf SYNTH_FLAGS
    }

    # Convert programming image to RDP format
    if { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "RPD_ASX4"} {
        nb_convert_to_rpd SYNTH_FLAGS
    }

    # Convert programming image to OFS_PMCI format
    if { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "OFS_PMCI"} {
        nb_run_ofs_pmci_script SYNTH_FLAGS
    }

    # Create .nfw archive
    nb_nfw_archive_create SYNTH_FLAGS
}

proc nb_convert_to_rbf {synth_flags} {
    global env
    upvar 1 $synth_flags SYNTH_FLAGS

    # Run quartus_pfg utility
    if {[catch {exec quartus_pfg -c $SYNTH_FLAGS(OUTPUT).sof $SYNTH_FLAGS(OUTPUT).rbf} msg]} {
        puts stderr "Converting the firmware file failed:\n$msg"
    }
}

proc nb_convert_to_rpd {synth_flags} {
    global env
    upvar 1 $synth_flags SYNTH_FLAGS

    # Run quartus_pfg utility
    if {[catch {exec quartus_pfg -c $SYNTH_FLAGS(OUTPUT).sof $SYNTH_FLAGS(OUTPUT).rpd -o mode=ASX4 -o bitswap=OFF} msg]} {
        puts stderr "Converting the firmware file failed:\n$msg"
    }
}

proc nb_run_ofs_pmci_script {synth_flags} {
    global env
    upvar 1 $synth_flags SYNTH_FLAGS

    file copy -force $SYNTH_FLAGS(OUTPUT).sof fpga.sof
    exec cp -rf $SYNTH_FLAGS(OFS_PMCI_SCRIPT_DIR) ./
    puts "Run OFS PMCI script..."
    exec -ignorestderr ./scripts/build_flash.sh
}

proc nb_nfw_archive_create {synth_flags} {
    global env
    upvar 1 $synth_flags SYNTH_FLAGS

    # Create temporary directory
    file mkdir $env(NETCOPE_TEMP)build_save_design

    # List of target files to be copied
    lappend NFW_FILES

    # Add output bitstream to .nfw archive
    if { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "RBF"} {
        lappend SYNTH_FLAGS(NFW_FILES) [list $SYNTH_FLAGS(OUTPUT).rbf $SYNTH_FLAGS(FPGA).rbf]
    } elseif { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "RPD_ASX4"} {
        lappend SYNTH_FLAGS(NFW_FILES) [list $SYNTH_FLAGS(OUTPUT).rpd $SYNTH_FLAGS(FPGA).rpd]
    } elseif { [info exist SYNTH_FLAGS(BITSTREAM)] && $SYNTH_FLAGS(BITSTREAM) == "OFS_PMCI"} {
        lappend SYNTH_FLAGS(NFW_FILES) [list fpga_page2_pacsign_user2.bin $SYNTH_FLAGS(FPGA).bin]
    } else {
        lappend SYNTH_FLAGS(NFW_FILES) [list $SYNTH_FLAGS(OUTPUT).sof $SYNTH_FLAGS(FPGA).sof]
    }

    # Copy each file from SYNTH_FLAGS(NFW_FILES) list to temporary directory
    foreach f $SYNTH_FLAGS(NFW_FILES) {
        file copy [lindex $f 0] $env(NETCOPE_TEMP)build_save_design/[lindex $f 1]
        lappend NFW_FILES [lindex $f 1]
    }

    # Run tar utility (obsolete .tar.gz file format, will be removed in the future)
    if {[catch {exec tar -czf $SYNTH_FLAGS(OUTPUT).tar.gz -C $env(NETCOPE_TEMP)build_save_design {*}$NFW_FILES} msg]} {
        puts stderr "Packaging the firmware file failed:\n$msg"
    }
    # Run tar utility (new .nfw file format)
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

    set fp [open $SYNTH_FLAGS(OUTPUT).sta.rpt]
    # Search the file for the sentence
    while {[gets $fp line] >= 0} {
        if {[regexp "Timing requirements not met" $line]} {
            puts "Timing constraints were NOT met!"
            seek $fp 0
            # Search the file for TNS and WNS
            while {[gets $fp line] >= 0} {
                if {[regexp "; Setup Summary" $line]} {
                    gets $fp line
                    gets $fp line
                    gets $fp line
                    gets $fp line
                    set WNSTNS [regexp -all -inline {\S+} $line]
                    puts -nonewline "WNS = "
                    puts [lindex $WNSTNS 3]
                    puts -nonewline "TNS = "
                    puts [lindex $WNSTNS 5]
                    return -code error
                }
            }
            return -code error
        }
    }
    puts "All constraints were met."
}

# -----------------------------------------------------------------------------
# Procedure SynthesizeProject
# Automaticly performs all previosly defined procedures. Alternatively, a user
# can manualy call previously defined procedures and use additional commands to
# customize synthesis process.
#
proc SynthesizeProject {synth_flags hierarchy} {
    # Define auxiliary variables
    upvar 1 $synth_flags SYNTH_FLAGS
    upvar 1 $hierarchy HIERARCHY

    # Set design parameters
    SetupDesign SYNTH_FLAGS

    # Add input files
    AddInputFiles SYNTH_FLAGS HIERARCHY

    # Set synthesis parameters, perform IP generation and perform design synthesis
    SynthesizeDesign SYNTH_FLAGS

    # Set implementation parameters and perform design implementation
    ImplementDesign SYNTH_FLAGS

    if {!$SYNTH_FLAGS(PROJ_ONLY) && !$SYNTH_FLAGS(SYNTH_ONLY)} {
        # Save implemented design
        SaveDesign SYNTH_FLAGS

        # Check design timing after implementation
        CheckTiming SYNTH_FLAGS
    }
}

proc qip_EvalFile {FNAME OPT} {
    set opt(LIBRARY) "work"
    array set opt $OPT

    lappend LIB_PARAM
    if {$opt(LIBRARY) != "work"} {
        lappend LIB_PARAM "-library" $opt(LIBRARY)
    }

    set FEXT [file extension $FNAME]

    set filedesc [open "Quartus.qip" "a+"]
    if {$opt(TYPE) == ""} {
        if {$FEXT == ".vhd"} {
            puts $filedesc [concat "set_global_assignment -name VHDL_FILE $FNAME -hdl_version VHDL_2008" {*}$LIB_PARAM]
        } elseif {$FEXT == ".sv"} {
            puts $filedesc "set_global_assignment -name SYSTEMVERILOG_FILE $FNAME"
        } elseif {$FEXT == ".v"} {
            puts $filedesc "set_global_assignment -name VERILOG_FILE $FNAME"
        } elseif {$FEXT == ".sdc"} {
            puts $filedesc "set_global_assignment -name SDC_FILE $FNAME"
        } elseif {$FEXT == ".ip"} {
            puts $filedesc "set_global_assignment -name IP_FILE $FNAME"
        } elseif {$FEXT == ".qsf"} {
            puts $filedesc "source $FNAME"
        } else {
            # Not yet supported file type for QIP
            puts "WARNING: Adding $FEXT files to the QIP file list is not yet supported."
        }
    } elseif {$opt(TYPE) == "CONSTR_QUARTUS"} {
        if {[info exists opt(SDC_ENTITY_FILE)]} {
            puts $filedesc "set_instance_assignment -entity $opt(SDC_ENTITY_FILE) -name SDC_ENTITY_FILE $FNAME"
        }
    }
    close $filedesc
}

proc qip_init {} {
    open "Quartus.qip" "w"
}

proc target_qip {} {
    global SYNTH_FLAGS HIERARCHY
    qip_init
    AddInputFiles SYNTH_FLAGS HIERARCHY "qip_EvalFile" {}
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

    set SYNTH_FLAGS(TOOL) "quartus"

    # Set default values
    if {![info exists SYNTH_FLAGS(PROJ_ONLY)]} {
        set SYNTH_FLAGS(PROJ_ONLY) false
    }
    if {![info exists SYNTH_FLAGS(SYNTH_ONLY)]} {
        set SYNTH_FLAGS(SYNTH_ONLY) false
    }
    if {![info exist SYNTH_FLAGS(VIRTUAL_PINS)]} {
        set SYNTH_FLAGS(VIRTUAL_PINS) false
    }
    if {![info exist SYNTH_FLAGS(ASSERT_OFF)]} {
        set SYNTH_FLAGS(ASSERT_OFF) false
    }

    if {[info exist SYNTH_FLAGS(QIP_ENABLE)]} {
        # Generate qip file in target_makefile by default: add to extra list
        lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_INIT)      qip_init
        lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_FILE) qip_EvalFile
    }
    # INFO: This is only a temporary solution
    lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_COMP) EvalComp
}

nb_sanitize_vars SYNTH_FLAGS HIERARCHY
