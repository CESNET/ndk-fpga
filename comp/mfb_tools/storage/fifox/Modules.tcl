# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET z. s. p. o.
# Author(s): Michal Szabo <xszabo11@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set FIFOX_BASE "$OFM_PATH/comp/base/fifo/fifox"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set COMPONENTS [list \
   [list "fifox" $FIFOX_BASE "behavioral" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_fifox.vhd"
