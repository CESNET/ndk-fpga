# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2022 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set OPEN_LOOP_BASE "$OFM_PATH/comp/base/async/open_loop"

lappend COMPONENTS [list "ASYNC_OPEN_LOOP" $OPEN_LOOP_BASE "FULL"]

lappend MOD "$ENTITY_BASE/led_ctrl_adv.vhd"
