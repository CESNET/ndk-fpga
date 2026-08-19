# Modules.tcl
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>,
#
# SPDX-License-Identifier: BSD-3-Clause

set ASYNC_RESET_BASE "$OFM_PATH/comp/base/async/reset"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS [ list "ASYNC_RESET"     "$ASYNC_RESET_BASE"     "FULL" ]

lappend MOD "$ENTITY_BASE/noc_init_ent.vhd"
if {$ARCHGRP == 256} {
    lappend MOD "$ENTITY_BASE/noc_init_256b.vhd"
} else {
    lappend MOD "$ENTITY_BASE/noc_init_512b.vhd"
}
lappend MOD "$ENTITY_BASE/hbm_fb2cdg1_reset.vhd"
lappend MOD "$ENTITY_BASE/hbm_fb2cdg1.vhd"
