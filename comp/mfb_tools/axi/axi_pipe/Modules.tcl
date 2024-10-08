# Modules.tcl: Components include script
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): Radek Hajek <hajek@brnologic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PIPE_BASE   "$OFM_PATH/comp/base/misc/pipe"

lappend COMPONENTS [list "PIPE"    $PIPE_BASE     "FULL"]

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend MOD "$ENTITY_BASE/axi_pipe.vhd"
