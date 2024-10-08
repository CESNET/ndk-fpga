# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set EDGE_DETECT_BASE    "$OFM_PATH/comp/base/logic/edge_detect"
set OR_BASE             "$OFM_PATH/comp/base/logic/or"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "EDGE_DETECT"        $EDGE_DETECT_BASE       "FULL" ]
lappend COMPONENTS [ list "OR"                 $OR_BASE                "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/emif_refresh.vhd"
