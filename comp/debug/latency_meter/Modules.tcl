# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOX_BASE     "$OFM_PATH/comp/base/fifo/fifox"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "FIFOX"       $FIFOX_BASE      "FULL" ]

lappend MOD "$ENTITY_BASE/latency_meter.vhd"
