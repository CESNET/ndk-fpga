# DevTree.tcl: Dev tree of stats component
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# 1. base 		- base address on MI bus
# 2. id  		- stats id
# 3. compatible	- compatible
proc data_logger {base id compatible} {
	set    ret ""
	append ret "$compatible" "_$id {"
	append ret "reg = <$base 0x30>;"
	append ret "compatible = \"netcope,$compatible\";"
	append ret "};"
	return $ret
}
