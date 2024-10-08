# Modules.tcl: Modules.tcl script to compile all design
# Copyright (C) 2016 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# PACKAGES:
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set DSP    "$OFM_PATH/comp/base/dsp/dsp_counter"

set COMPONENTS [list \
    [list "DSP"    $DSP     "FULL"] \
]

# MODULES:
if { $ARCHGRP == "FULL" } {
  set MOD "$MOD $ENTITY_BASE/inspector_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/inspector.vhd"
}
