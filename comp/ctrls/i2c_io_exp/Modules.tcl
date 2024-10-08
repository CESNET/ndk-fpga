# Modules.tcl: Local include Modules script
# Copyright (C) 2022 CESNET
# Author: Stepan Friedl <friedl@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set IIC_BASE "$OFM_PATH/comp/ctrls/i2c_hw"
set OL_BASE  "$OFM_PATH/comp/base/async/open_loop"

set COMPONENTS [ list \
    [ list "I2C"       $IIC_BASE "FULL" ] \
    [ list "OPEN LOOP" $OL_BASE  "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/io_exp.vhd"

