# Modules.tcl: Local include script
# Copyright (C) 2016 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set SV_CRC_BASE      "$OFM_PATH/../modules/internal/base/ff/crc32"
set SV_COMMON_BASE   "$OFM_PATH/comp/ver"

set COMPONENTS [list \
    [ list "SV_CRC"    $SV_CRC_BASE    "ETHERNET"] \
    [ list "SV_COMMON" $SV_COMMON_BASE "FULL"] \
]

lappend MOD "$ENTITY_BASE/sv_mii_pkg.sv"
