# Modules.tcl: Local include Modules script
# Copyright (C) 2009 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

set ASYNC_RESET_BASE     "$OFM_PATH/comp/base/async/reset/"

set COMPONENTS [list \
   [list "I2C_HW"        "$ENTITY_BASE/.."   "FULL"] \
   [list "ASYNC_RESET"   $ASYNC_RESET_BASE   "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/i2c_mi32.vhd"

