# demux.vhd: General width MVB DEMUX
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set DEC1FN_BASE         "$OFM_PATH/comp/base/logic/dec1fn"
set MVB_FORK_BASE       "$OFM_PATH/comp/mvb_tools/flow/fork"
set MVB_DISCARD_BASE    "$OFM_PATH/comp/mvb_tools/flow/discard"


# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "DEC1FN"      $DEC1FN_BASE        "FULL" ]
lappend COMPONENTS [ list "MVB_FORK"    $MVB_FORK_BASE      "FULL" ]
lappend COMPONENTS [ list "MVB_DISCARD" $MVB_DISCARD_BASE      "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/demux.vhd"
lappend MOD "$ENTITY_BASE/demux2.vhd"
