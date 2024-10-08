# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Base directories

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list \
    [list "SDP_BRAM" $OFM_PATH/comp/base/mem/sdp_bram "behavioral" ] \
]

set MOD "$MOD $ENTITY_BASE/fifo_bram.vhd"
