# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET z. s. p. o.
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# list of sub-components
set COMPONENTS [ list \
    [ list "MFB_MERGER_GEN" "$ENTITY_BASE/../.." "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/dut_wrapper.vhd"
