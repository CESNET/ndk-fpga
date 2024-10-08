# Shared.tcl: Common procedures for generating SV package generator
# Copyright (C) 2023 CESNET
# Author: Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

proc SvPkgConst {name value} {
	global SV_PKG_CONTENT
	append SV_PKG_CONTENT "   parameter $name = $value;\n"
}
proc setConst {name value} {
	global $name
	set $name $value
}

proc setSvPkgOth      {name value} { SvPkgConst $name $value; setConst $name $value }
proc setSvPkgStr      {name value} { SvPkgConst $name "\"$value\""; setConst $name $value }

proc    SvPkgStr      {name value} { SvPkgConst $name "\"$value\"" }

proc    VhdlPkgHexVector {name size value} {VhdlPkgVector $name $size "X\"$value\"" }
proc    VhdlPkgBinVector {name size value} {VhdlPkgVector $name $size "b\"$value\"" }

proc SvPkgBegin { } {
	global SV_PKG_CONTENT
	set SV_PKG_CONTENT ""
}
proc SvPkgFinish { PATH NAME } {
	global SV_PKG_CONTENT
    set USER_CONST [file rootname [file tail $PATH]]

	set CONTENT "// This file was generated automatically. For changing its content,
// edit corresponding variables in $USER_CONST.tcl

package $NAME;\n
$SV_PKG_CONTENT
endpackage $NAME;
"
    nb_file_update $PATH $CONTENT
}

proc nb_generate_file_register_userpkg {{pkgname "combo_user_const"} {filename ""} {prereq ""}} {
    if {$filename == ""} {
        global env
        set filename $env(NETCOPE_TEMP)netcope_const.sv
    }
    return [nb_generate_file_register $filename SvPkgFinish [list $filename $pkgname] $prereq "phony"]
}
