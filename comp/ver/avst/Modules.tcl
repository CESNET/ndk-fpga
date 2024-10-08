# Modules.tcl: Local include script
# Copyright (C) 2020 CESNET
# Author: Radek Iša <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set COMPONENTS [ list \
    [list "SV_COMMON" "$OFM_PATH/comp/ver"           "FULL"]\
]



set MOD "$MOD $ENTITY_BASE/rx/pkg.sv"
set MOD "$MOD $ENTITY_BASE/tx/pkg.sv"


