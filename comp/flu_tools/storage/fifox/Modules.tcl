# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Michal Szabo <xszabo11@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Components
set COMPONENTS [ list \
    [ list "FIFOX" $OFM_PATH/comp/base/fifo/fifox "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/flu_fifox.vhd"
