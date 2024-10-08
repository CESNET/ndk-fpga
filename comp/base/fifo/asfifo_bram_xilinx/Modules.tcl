# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [ list \
    [ list "MATH_PACK" "$OFM_PATH/comp/base/pkg"               "MATH" ] \
    [ list "TYPE_PACK" "$OFM_PATH/comp/base/pkg"               "TYPE" ] \
    [ list "SHREG"     "$OFM_PATH/comp/base/shreg/sh_reg_base" "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/asfifo_bram_xilinx.vhd"

lappend SRCS(CONSTR_VIVADO) [list $ENTITY_BASE/asfifo_bram_xilinx.xdc SCOPED_TO_REF ASFIFO_BRAM_XILINX]
