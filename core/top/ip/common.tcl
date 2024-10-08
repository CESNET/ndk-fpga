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
        if {[string tolower $ip_params(IP_DEVICE_FAMILY)] eq "agilex"} {
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

        # prevent regeneration of IP files if present (and generated correctly)
        # (Quartus only, TODO: add similar logic for Vivado (does not use .xci files generation by default))
        set ip_file $ip_params_mod(IP_BUILD_DIR)/[get_ip_filename $comp]
        if {[file exists $ip_file]} {
            if {$use_quartus && ![file exists $ip_params_mod(IP_MODIFY_BASE)/$script\_ip.qpf]} {
                lappend ip_files_l $ip_file
                continue
            }
        }

        # provide additional IP parameters
        set ip_params_mod(IP_COMP_NAME) $comp
        set ip_params_mod(IP_COMP_TYPE) $type

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
    }

    return $ip_files_l
}
