# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set FIFOX_BASE "$OFM_PATH/comp/base/fifo/fifox"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set COMPONENTS [list \
    [list "FIFOX" $FIFOX_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/pcie_avst2mfb.vhd"
