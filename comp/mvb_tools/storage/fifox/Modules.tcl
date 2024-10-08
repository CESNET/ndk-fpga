# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2018 CESNET z. s. p. o.
# Author: Michal Szabo <xszabo11@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

#Set paths
set FIFO_BASE        "$OFM_PATH/comp/base/fifo/fifox"

# Entities
set MOD "$MOD $ENTITY_BASE/mvb_fifox.vhd"

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Subcomponents
set COMPONENTS [ list \
    [list "FIFOX" $FIFO_BASE "FULL"] \
]
