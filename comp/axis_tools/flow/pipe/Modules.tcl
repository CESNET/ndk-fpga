# Modules.tcl: Components include script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2025
#
# SPDX-License-Identifier: BSD-3-Clause

set PIPE_BASE   "$OFM_PATH/comp/base/misc/pipe"

lappend COMPONENTS [list "PIPE"    $PIPE_BASE     "FULL"]

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend MOD "$ENTITY_BASE/axis_pipe.vhd"
