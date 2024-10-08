# Modules.tcl: Component include tcl script.
# Copyright (C) 2014 CESNET
# Author: Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PIPE_BASE      "$OFM_PATH/comp/base/misc/pipe"
set FLU_PIPE_BASE  "$OFM_PATH/comp/flu_tools/flow/pipe"

set COMPONENTS [ list \
   [ list "PIPE"       $PIPE_BASE      "FULL"]\
   [ list "FLU_PIPE"   $FLU_PIPE_BASE  "FULL"]\
]

set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
set MOD "$ENTITY_BASE/axi2flu.vhd"
