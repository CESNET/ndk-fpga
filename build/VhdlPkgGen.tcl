# ----- Common procedures for generating VHDL package generator -----------

proc VhdlPkgConst {name type value} {
	global VHDL_PKG_CONTENT
	append VHDL_PKG_CONTENT "   constant $name : $type := $value;\n"
}
proc setConst {name value} {
	global $name
	set $name $value
}

proc setVhdlPkgInt    {name value} { VhdlPkgConst $name integer $value; setConst $name $value }
proc setVhdlPkgBool   {name value} { VhdlPkgConst $name boolean $value; setConst $name $value }
proc setVhdlPkgReal   {name value} { VhdlPkgConst $name real    $value; setConst $name $value }
proc setVhdlPkgStr    {name value} { VhdlPkgConst $name "string" "\"$value\""; setConst $name $value }
proc    VhdlPkgInt    {name value} { VhdlPkgConst $name integer $value }
proc    VhdlPkgIntArr {name size} {
			set type [concat "integer_vector(" [expr $size - 1] "downto 0)"]
			upvar $name array
			set value "("
			if {$size == 1} {
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
	   		VhdlPkgConst $name $type $value
		}
proc    VhdlPkgBool   {name value} { VhdlPkgConst $name boolean $value }
proc    VhdlPkgReal   {name value} { VhdlPkgConst $name real    $value }
proc    VhdlPkgStr    {name value} { VhdlPkgConst $name "string" "\"$value\"" }
proc    VhdlPkgVector {name size value} {
			set str [concat "std_logic_vector(" [expr $size - 1] "downto 0)"]
	   		VhdlPkgConst $name $str $value
		}
proc    VhdlPkgHexVector {name size value} {VhdlPkgVector $name $size "X\"$value\"" }
proc    VhdlPkgBinVector {name size value} {VhdlPkgVector $name $size "\"$value\"" }

proc VhdlPkgProjectText s {
	global DT_PROJECT_TEXT
	set DT_PROJECT_TEXT $s
    binary scan $s H* hex
    set hex [regsub -all (..) $hex {\1}]
    append hex [string repeat 00 [expr 32 - [string length $s]]]
	VhdlPkgVector ID_PROJECT_TEXT 256 "X\"$hex\""
	# For NetCope, which uses generic passing (100G1 at this moment)
	global ID_PROJECT_TEXT
	set ID_PROJECT_TEXT "256'h$hex"
}

proc VhdlPkgBegin { } {
	global VHDL_PKG_CONTENT
	set VHDL_PKG_CONTENT ""
}
proc VhdlPkgFinish { PATH NAME } {
	global VHDL_PKG_CONTENT
    set USER_CONST [file rootname [file tail $PATH]]

	set CONTENT "-- This file was generated automatically. For changing its content,
-- edit corresponding variables in $USER_CONST.tcl

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;

package $NAME is
$VHDL_PKG_CONTENT
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
