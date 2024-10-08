# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MVB_FORK_BASE       "$OFM_PATH/comp/mvb_tools/flow/fork"
set MVB_FIFOX_BASE      "$OFM_PATH/comp/mvb_tools/storage/fifox"
set MVB_DISCARD_BASE    "$OFM_PATH/comp/mvb_tools/flow/discard"
set MVB_PIPE_BASE       "$OFM_PATH/comp/mvb_tools/flow/pipe"

lappend PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES  "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "MVB_FORK"            $MVB_FORK_BASE          "FULL" ]
lappend COMPONENTS [ list "MVB_DISCARD"         $MVB_DISCARD_BASE       "FULL" ]
lappend COMPONENTS [ list "MVB_FIFOX"           $MVB_FIFOX_BASE         "FULL" ]
lappend COMPONENTS [ list "MVB_PIPE"            $MVB_PIPE_BASE          "FULL" ]

lappend MOD "$ENTITY_BASE/mvb_operation.vhd"
