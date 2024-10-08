# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2020 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASFIFOX_BASE "$OFM_PATH/comp/base/fifo/asfifox"
set RESET_BASE   "$OFM_PATH/comp/base/async/reset"

set COMPONENTS [ list\
    [ list "ASFIFOX"     $ASFIFOX_BASE "FULL"      ] \
    [ list "ASYNC_RESET" $RESET_BASE   "FULL"      ] \
]

set MOD "$MOD $ENTITY_BASE/mi_async.vhd"

