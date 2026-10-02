# Modules.tcl: Components include script for DRAM_FIFO
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFOX_BASE           "$OFM_PATH/comp/base/fifo/fifox"
set AXIS_FIFO_BASE       "$OFM_PATH/comp/axis_tools/storage/fifo"
set AXIS_PACKET_LEN_BASE "$OFM_PATH/comp/axis_tools/logic/packet_len"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "FIFOX"           $FIFOX_BASE           "FULL" ]
lappend COMPONENTS [ list "AXIS_FIFO"       $AXIS_FIFO_BASE       "FULL" ]
lappend COMPONENTS [ list "AXIS_PACKET_LEN" $AXIS_PACKET_LEN_BASE "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/dram_fifo.vhd"

