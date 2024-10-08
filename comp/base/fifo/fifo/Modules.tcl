# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set COMPONENTS [list \
    [list "PKG"        "$OFM_PATH/comp/base/pkg"                "MATH"] \
    [list "DISTMEM"    "$OFM_PATH/comp/base/mem/gen_lutram/compatibility" "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/fifo_ent.vhd"
set MOD "$MOD $ENTITY_BASE/fifo.vhd"
