# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set FIFO_BASE "$OFM_PATH/comp/base/fifo"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "REG_FIFO" "$FIFO_BASE/reg_fifo" "FULL" ]
lappend COMPONENTS [ list "FIFOX"    "$FIFO_BASE/fifox"    "FULL" ]

lappend MOD "$ENTITY_BASE/fifo.vhd"
