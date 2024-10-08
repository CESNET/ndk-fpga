# DevTree.tcl: Dev tree of mem-tester component
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# 1. base 	- base address on MI bus
# 2. id  	- mem tester id
proc mem_tester {base id} {
	set    ret ""
	append ret "mem_tester_$id {"
	append ret "reg = <$base 0x100>;"
	append ret "compatible = \"netcope,mem_tester\";"
	append ret "};"
	return $ret
}
