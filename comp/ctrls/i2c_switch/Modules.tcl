# Modules.tcl: Local include Modules script
# Copyright (C) 2024 CESNET
# Author: Stepan Friedl <friedl@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set IIC_BASE "$OFM_PATH/comp/ctrls/i2c_hw"

set COMPONENTS [ list \
    [ list "I2C"       $IIC_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/i2c_switch.vhd"
