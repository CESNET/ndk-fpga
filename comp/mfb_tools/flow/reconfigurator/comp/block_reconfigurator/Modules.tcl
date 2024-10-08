# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2020 CESNET
# Author: Jan Kubalek <kubalek@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause
# packages:
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# components:
set COMPONENTS [list\
    [list "REGION_RECONF"       "$ENTITY_BASE/../region_reconfigurator"                       "FULL"]\
]

# modules:
set MOD "$MOD $ENTITY_BASE/block_reconfigurator.vhd"
