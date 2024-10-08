# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2020 CESNET
# Author: Jan Kubalek <kubalek@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause
# packages:
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# components:
set COMPONENTS [list\
    [list "TRANSFORMER"       "$OFM_PATH/comp/mfb_tools/flow/transformer"               "FULL"]\
    [list "REGION_RECONF"     "$ENTITY_BASE/comp/region_reconfigurator"             "FULL"]\
    [list "BLOCK_RECONF"      "$ENTITY_BASE/comp/block_reconfigurator"              "FULL"]\
    [list "ITEM_RECONF"       "$ENTITY_BASE/comp/item_reconfigurator"               "FULL"]\
]

# modules:
set MOD "$MOD $ENTITY_BASE/mfb_reconfigurator.vhd"
