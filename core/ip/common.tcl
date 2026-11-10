# common.tcl: script with common IP functionality
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc get_ip_filename {ip_name {synth "QUARTUS"}} {
    if {$synth == "QUARTUS"} {
        return $ip_name.ip
    } elseif {$synth == "VIVADO"} {
        return $ip_name.xci
    }
}

# Returns the IP parameters and the content of the IP scripts as one string.
# A generated IP is reused only when this string has not changed.
proc get_ip_stamp {ip_params_l scripts_l} {
    set stamp [lsort -stride 2 -index 0 $ip_params_l]
    foreach script $scripts_l {
        if {[file exists $script]} {
            set fd [open $script r]
            append stamp "\n" [read $fd]
            close $fd
        }
    }
    return $stamp
}

proc get_ip_mod_files {ip_components_l ip_params_l} {
    array set ip_params $ip_params_l
    set ip_files_l [list]
    set use_ip_subdirs false
    set build_dir_diff true
    set use_quartus false

    if {[info exists ip_params(USE_IP_SUBDIRS)]} {
        set use_ip_subdirs $ip_params(USE_IP_SUBDIRS)
    }

    if {[file normalize $ip_params(IP_BUILD_DIR)] eq [file normalize $ip_params(IP_MODIFY_BASE)]} {
        set build_dir_diff false
    }

    if {[info exists ip_params(IP_DEVICE_FAMILY)]} {
        if {[string tolower $ip_params(IP_DEVICE_FAMILY)] eq "agilex" || [string tolower $ip_params(IP_DEVICE_FAMILY)] eq "stratix 10"} {
            set use_quartus true
        }
    }

    foreach ip_comp $ip_components_l {
        # subdirectory under IP templates folder (used to organize scripts)
        set path   [lindex $ip_comp 0]
        # script name (same for template and for modification script)
        set script [lindex $ip_comp 1]
        # IP component name (used in HDL code)
        set comp   [lindex $ip_comp 2]
        # used to generate multiple IPs with different parameters (e. g. ia420f - onboard_ddr4)
        set type   [lindex $ip_comp 3]
        # adjust generated template according to provided IP modification file (for Vivado use modification scripts only)
        set modify [lindex $ip_comp 4]

        # make adjustments when using subdirectories
        array set ip_params_mod [array get ip_params]
        if {$use_ip_subdirs} {
            set ip_subdir $ip_params(IP_MODIFY_BASE)/$script
            set ip_params_mod(IP_MODIFY_BASE) $ip_subdir
            if {!$build_dir_diff} {
                set ip_params_mod(IP_BUILD_DIR) $ip_subdir
            }
        }

        # provide additional IP parameters
        set ip_params_mod(IP_COMP_NAME) $comp
        set ip_params_mod(IP_COMP_TYPE) $type

        # prevent regeneration of IP files if present (and generated correctly with the same parameters and scripts)
        # (Quartus only, TODO: add similar logic for Vivado (does not use .xci files generation by default))
        set ip_file $ip_params_mod(IP_BUILD_DIR)/[get_ip_filename $comp]
        if {$use_quartus} {
            set ip_scripts_l [list "$ip_params_mod(IP_TEMPLATE_BASE)/$path/$script.ip.tcl"]
            if {$modify == 1} {
                lappend ip_scripts_l "$ip_params_mod(IP_MODIFY_BASE)/$script.ip.tcl"
            }
            set ip_stamp [get_ip_stamp [array get ip_params_mod] $ip_scripts_l]
            set ip_stamp_file $ip_file.params
            set ip_stamp_old ""
            if {[file exists $ip_stamp_file]} {
                set fd [open $ip_stamp_file r]
                set ip_stamp_old [read $fd]
                close $fd
            }
            if {[file exists $ip_file] && ![file exists $ip_params_mod(IP_MODIFY_BASE)/$script\_ip.qpf] && $ip_stamp_old eq $ip_stamp} {
                lappend ip_files_l $ip_file
                continue
            }
            # The old IP file, its generated files and its parameters are deleted, so a build that fails
            # before the end of the generation cannot reuse them.
            # qsys-script cannot create the IP again while the directory exists.
            file delete $ip_file $ip_stamp_file
            file delete -force [file rootname $ip_file]
        }

        set script_type [expr {$use_quartus? "QUARTUS_TCL" : "VIVADO_TCL"}]
        # add IP template script (Quartus only)
        if {$use_quartus} {
            lappend ip_files_l [list                                    \
                "$ip_params_mod(IP_TEMPLATE_BASE)/$path/$script.ip.tcl" \
                TYPE $script_type                                       \
                PHASE { "ADD_FILES" "IP_TEMPLATE_GEN" }                 \
                IP_BUILD_DIR $ip_params_mod(IP_BUILD_DIR)               \
                VARS [list IP_PARAMS_L [array get ip_params_mod]]       \
            ]
        }

        # add IP modification script
        if {$modify == 1} {
            lappend ip_files_l [list                                    \
                "$ip_params_mod(IP_MODIFY_BASE)/$script.ip.tcl"         \
                TYPE $script_type                                       \
                PHASE { "ADD_FILES" "IP_MODIFY" }                       \
                IP_BUILD_DIR $ip_params_mod(IP_BUILD_DIR)               \
                VARS [list IP_PARAMS_L [array get ip_params_mod]]       \
            ]
        }

        # The last script of the IP writes its parameters to IP_STAMP_FILE after it ends without an error.
        if {$use_quartus} {
            set ip_last_script [lindex $ip_files_l end]
            lappend ip_last_script IP_STAMP_FILE $ip_stamp_file IP_STAMP $ip_stamp
            lset ip_files_l end $ip_last_script
        }
    }

    return $ip_files_l
}
