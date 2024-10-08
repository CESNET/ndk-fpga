# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2017 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $OFM_PATH/comp/base/pkg/math_pack.vhd"
    set MOD "$MOD $ENTITY_BASE/flu_generator.vhd"
}
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
