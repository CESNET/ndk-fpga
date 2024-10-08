# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2018 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set FIRST_ONE_BASE "$OFM_PATH/comp/base/logic/first_one"

set COMPONENTS [list \
   [list "FIRST_ONE" $FIRST_ONE_BASE "FULL"] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/last_one.vhd"
