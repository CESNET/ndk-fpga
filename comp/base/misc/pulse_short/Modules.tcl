# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Remote components
set COMPONENTS [list \
    [list "ASYNC_GENERAL" "$OFM_PATH/comp/base/async/general" "FULL"] \
    [list "ASYNC_OPEN_LOOP" "$OFM_PATH/comp/base/async/open_loop" "FULL"] \
    [list "ASYNC_RESET" "$OFM_PATH/comp/base/async/reset" "FULL"] \
]

# Local components
lappend MOD "$ENTITY_BASE/pulse_short.vhd"
