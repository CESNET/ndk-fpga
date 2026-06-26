# ----- Common procedures for generating VHDL package generator -----------

# Default package name for backward compatibility.
set VHDL_PKG_DEFAULT "combo_user_const"

# Extract optional -pkg argument from the front of an argument list.
# Returns the selected package name and modifies 'args_var' so that it
# contains the remaining arguments.
proc VhdlPkgGetPkgName { args_var } {
    upvar $args_var args
    global VHDL_PKG_DEFAULT

    set pkg $VHDL_PKG_DEFAULT
    while { [llength $args] >= 2 } {
        set arg [lindex $args 0]
        if { $arg eq "-pkg" } {
            set pkg [lindex $args 1]
            set args [lrange $args 2 end]
        } else {
            break
        }
    }
    return $pkg
}

proc VhdlPkgConst { args } {
    global VHDL_PKG_CONTENT
    set pkg [VhdlPkgGetPkgName args]
    set name [lindex $args 0]
    set type [lindex $args 1]
    set value [lindex $args 2]

    if { ![info exists VHDL_PKG_CONTENT($pkg)] } {
        set VHDL_PKG_CONTENT($pkg) ""
    }
    append VHDL_PKG_CONTENT($pkg) "   constant $name : $type := $value;\n"
}

proc _VhdlPkgConstSimple {do_set type args} {
    set pkg [VhdlPkgGetPkgName args]
    lassign $args name value
    if {$do_set} {
        global $name
        set $name $value
    }
    if {$type eq "string"} {
        set value "\"$value\""
    }
    VhdlPkgConst -pkg $pkg $name $type $value
}

proc VhdlPkgInt  {args} { _VhdlPkgConstSimple 0 integer {*}$args }
proc VhdlPkgBool {args} { _VhdlPkgConstSimple 0 boolean {*}$args }
proc VhdlPkgReal {args} { _VhdlPkgConstSimple 0 real    {*}$args }
proc VhdlPkgStr  {args} { _VhdlPkgConstSimple 0 string  {*}$args }

proc setVhdlPkgInt  {args} { _VhdlPkgConstSimple 1 integer {*}$args }
proc setVhdlPkgBool {args} { _VhdlPkgConstSimple 1 boolean {*}$args }
proc setVhdlPkgReal {args} { _VhdlPkgConstSimple 1 real    {*}$args }
proc setVhdlPkgStr  {args} { _VhdlPkgConstSimple 1 string  {*}$args }

proc VhdlPkgIntArr {args} {
    set pkg [VhdlPkgGetPkgName args]
    lassign $args name size
    set type [concat "integer_vector(" [expr $size - 1] "downto 0)"]
    upvar $name array
    set value "("
    if {$size == 0} {
        append value "others => 0"
    } elseif {$size == 1} {
        append value "others => " $array(0)
    } else {
        for {set index [expr $size-1]} {$index >= 0} {incr index -1} {
            append value $array($index)
            if {$index > 0} {
                append value ", "
            }
        }
    }
    append value ")"
    VhdlPkgConst -pkg $pkg $name $type $value
}

proc VhdlPkgVector {args} {
    set pkg [VhdlPkgGetPkgName args]
    lassign $args name size value
    set str [concat "std_logic_vector(" [expr $size - 1] "downto 0)"]
    VhdlPkgConst -pkg $pkg $name $str $value
}

proc _VhdlPkgVectorFmt {fmt args} {
    set pkg [VhdlPkgGetPkgName args]
    lassign $args name size value
    VhdlPkgVector -pkg $pkg $name $size [format $fmt $value]
}

proc VhdlPkgHexVector {args} { _VhdlPkgVectorFmt {X"%s"} {*}$args }
proc VhdlPkgBinVector {args} { _VhdlPkgVectorFmt {"%s"}  {*}$args }

proc VhdlPkgProjectText {args} {
    global DT_PROJECT_TEXT
    set pkg [VhdlPkgGetPkgName args]
    lassign $args s
    set DT_PROJECT_TEXT $s
    binary scan $s H* hex
    set hex [regsub -all (..) $hex {\1}]
    append hex [string repeat 00 [expr 32 - [string length $s]]]
    VhdlPkgVector -pkg $pkg ID_PROJECT_TEXT 256 "X\"$hex\""
    # For NetCope, which uses generic passing (100G1 at this moment)
    global ID_PROJECT_TEXT
    set ID_PROJECT_TEXT "256'h$hex"
}

proc VhdlPkgBegin { } {
    global VHDL_PKG_CONTENT VHDL_PKG_DEFAULT
    array set VHDL_PKG_CONTENT {}
    set VHDL_PKG_DEFAULT "combo_user_const"
    set VHDL_PKG_CONTENT(combo_user_const) ""
}
proc VhdlPkgFinish { PATH NAME } {
    global VHDL_PKG_CONTENT

    if { ![info exists VHDL_PKG_CONTENT($NAME)] } {
        set VHDL_PKG_CONTENT($NAME) ""
    }
    set pkg_content $VHDL_PKG_CONTENT($NAME)
    set USER_CONST [file rootname [file tail $PATH]]

    set CONTENT "-- This file was generated automatically. For changing its content,
-- edit corresponding variables in $USER_CONST.tcl

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;

package $NAME is
$pkg_content
end $NAME;

package body $NAME is
end $NAME;
"
    nb_file_update $PATH $CONTENT
}

proc nb_generate_file_register_userpkg {{pkgname "combo_user_const"} {filename ""} {prereq ""}} {
    if {$filename == ""} {
        global env
        set filename $env(NETCOPE_TEMP)netcope_const.vhd
    }
    return [nb_generate_file_register $filename VhdlPkgFinish [list $filename $pkgname] $prereq "phony"]
}
