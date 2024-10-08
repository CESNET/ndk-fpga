# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Louda <sandin@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set FL_BASE     "$OFM_PATH/comp/fl_tools"
set BMEM_BASE   "$OFM_PATH/comp/base/mem/dp_bmem"

set PACKAGES    "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Source files for all architectures
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"
set MOD "$MOD $OFM_PATH/comp/mi_tools/pkg/mi32_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/completer.vhd"
set MOD "$MOD $ENTITY_BASE/top/uh_completer.vhd"

# components
set COMPONENTS [list \
    [list "DP_BMEM" $BMEM_BASE  "FULL"] \
]
