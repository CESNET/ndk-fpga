# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2023 CESNET
# Author: Tomas Fukac <fukac@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [list \
    [ list "TCAM2" "$OFM_PATH/comp/base/mem/tcam2" "FULL" ] \
]

# Source file for tcam component
set MOD "$MOD $ENTITY_BASE/mvb_tcam.vhd"
