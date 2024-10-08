# targets.tcl: build system TCL script with common targets
# Copyright (C) 2019 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# -----------------------------------------------------------------------------
# Procedure nb_main
# Search for target specified by -t parameter and run TCL procedure with name
# in format "target_$name"
#
proc nb_main {} {
    global argv

    set TARGET_NAME "default"
    set TARGET_PARAMS [list ]
    getopt arg $argv {
        -t: - --target:TARGET {
            # Specify target name
            set TARGET_NAME $arg
        }
        -p: - --parameter:PARAM {
            # Add parameter for target
            lappend TARGET_PARAMS $arg
        }

        arglist {
            # Not used right now
        }
    }

    # Check if target exists
    if {[llength [info procs target_$TARGET_NAME]] > 0} {
        target_$TARGET_NAME {*}$TARGET_PARAMS
        exit 0
    } else {
        if {$TARGET_NAME == "default"} {
            # Fallback mode
            puts "INFO: TCL target $TARGET_NAME doesn't exists. Running rest of main TCL script."
        } elseif {$TARGET_NAME == "none"} {
            # Noop
        } else {
            puts "ERROR: TCL target $TARGET_NAME doesn't exists. Please define procedure target_$TARGET_NAME."
            exit 1
        }
    }
}

# -----------------------------------------------------------------------------
# Procedure nb_generate_file_register
# Declare, that there is a dynamically generated file: recipe for this file
# will be created in generated Makefile. Then if the 'filename' is used in
# project (e.g. in MOD or SYNTH_FLAG(CONSTR) vars), the make will call
# 'callback' proc through generate_file target.
# 'flag_list' values:
# * 'phony' - creates a PHONY target in Makefile
#
proc nb_generate_file_register {filename callback {callback_param_list ""} {prerequisites_list ""} {flag_list ""}} {
    global SYNTH_FLAGS
    lappend SYNTH_FLAGS(NB_GENERATED_FILES) [list $filename $callback $callback_param_list $prerequisites_list $flag_list]
    return $filename
}

proc DevTree_init {} {
    # INFO: Temporary workaround
    open "DevTree_paths.txt" "w"
}

proc EvalFileDevTree_paths {FNAME OPT} {
    array set opt $OPT

    if {$opt(TYPE) == "DEVTREE"} {
        set dt_paths [open "DevTree_paths.txt" "a+"]
        puts $dt_paths "$FNAME"
        close $dt_paths
    }
}

# ---------------------- Common targets -------------------------------
proc target_makefile {filename} {
    global SYNTH_FLAGS HIERARCHY NB_FLAGS

    # Sanitize TARGET_MAKEFILE_EXTRA items
    lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_INIT) DevTree_init
    lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_FILE) EvalFileDevTree_paths
    lappend SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_COMP)
    set NB_FLAGS(VERBOSITY) 0

    foreach init_proc $SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_INIT) {
        eval $init_proc
    }
    set NB_FILELIST [AddInputFiles SYNTH_FLAGS HIERARCHY $SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_FILE) $SYNTH_FLAGS(TARGET_MAKEFILE_EXTRA_EVAL_COMP)]

    set content ""

    foreach FILE $SYNTH_FLAGS(NB_GENERATED_FILES) {
        # Create full path as ApplyToMods do, because Makefile match exact path string
        set FILENAME [list ]
        foreach FULLNAME [lindex $FILE 0] {
            lappend FILENAME [SimplPath $FULLNAME]
        }
        set PREREQUISITES [lindex $FILE 3]
        if {"phony" in [lindex $FILE 4]} {
            append content ".PHONY: $FILENAME\n"
        }
        append content "$FILENAME: [join [lindex $FILE 3]]\n"
        append content "	@\$(NETCOPE_ENV) \$(TCLSH) \$(SYNTHFILES) -t generate_file -p \$@\n"
    }

    lappend skip_types "COMPONENT"
    append content "MOD := \\\n"
    foreach FILE [lreverse $NB_FILELIST] {
        array set opt [lassign $FILE FNAME]
        if {$opt(TYPE) ni $skip_types} {
            append content "    $FNAME \\\n"
        }
    }
    nb_file_update $filename $content
}

proc target_generate_file {filename} {
    PrintLabel "Generating source file: $filename"

    global SYNTH_FLAGS

    foreach GEN_FILE $SYNTH_FLAGS(NB_GENERATED_FILES) {
        foreach FILE [lindex $GEN_FILE 0] {
            if {[SimplPath $FILE] == $filename} {
                file mkdir [file dirname $FILE]
                [lindex $GEN_FILE 1] {*}[lindex $GEN_FILE 2]
                return
            }
        }
    }
    puts "ERROR: recipe for generating '$filename' not found!"
    exit 1
}

proc nb_targets_sanitize_vars {} {
    global SYNTH_FLAGS HIERARCHY
    lappend SYNTH_FLAGS(NB_GENERATED_FILES)
}

nb_targets_sanitize_vars
