# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set LAST_ONE_BASE           "$OFM_PATH/comp/base/logic/last_one"
set OR_BASE                 "$OFM_PATH/comp/base/logic/or"
set DEC1F_BASE              "$OFM_PATH/comp/base/logic/dec1fn"
set DP_BRAM_BASE            "$OFM_PATH/comp/base/mem/dp_bram"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "LAST_ONE"   $LAST_ONE_BASE  "FULL" ]
lappend COMPONENTS [ list "OR"         $OR_BASE        "FULL" ]
lappend COMPONENTS [ list "DEC1FN"     $DEC1F_BASE     "FULL" ]
lappend COMPONENTS [ list "DP_BRAM"    $DP_BRAM_BASE   "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/histogramer_types.vhd"
lappend MOD "$ENTITY_BASE/histogramer_old.vhd"
