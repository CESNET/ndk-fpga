# Modules.tcl: Local include tcl script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2025
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set COMPONENTS [ list \
    [ list "ASYNC_OPEN_LOOP"        "$OFM_PATH/comp/base/async/open_loop"      "FULL" ] \
    [ list "SH_REG_BASE_STATIC"     "$OFM_PATH/comp/base/shreg/sh_reg_base"    "FULL" ] \
    [ list "ASYNC_OPEN_LOOP_SMD"    "$OFM_PATH/comp/base/async/open_loop_smd"  "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/sync_fpga_id.vhd"
