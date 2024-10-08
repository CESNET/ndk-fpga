# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set COMPONENTS [ list \
    [ list "FIFO" "$OFM_PATH/comp/base/fifo/fifo_bram_xilinx" "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/fl_fifo_bram_xilinx.vhd"
