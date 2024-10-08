# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Petr Mikusek <petr.mikusek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# list of sub-components
set COMPONENTS [list \
   [list "PKG_MATH" $OFM_PATH/comp/base/pkg "MATH"] \
]

set MOD "$MOD $ENTITY_BASE/sh_fifo_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/sh_fifo.vhd"
