# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components

# Base directories

set COMPONENTS [list \
    [list "FIFO"         $OFM_PATH/comp/base/fifo/fifo       "FULL"]  \
]
set MOD "$MOD $ENTITY_BASE/../ib_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/ib_sim_oper.vhd"
set MOD "$MOD $ENTITY_BASE/ib_sim_loging.vhd"
set MOD "$MOD $ENTITY_BASE/write_align.vhd"
set MOD "$MOD $ENTITY_BASE/ib_sim.vhd"
set MOD "$MOD $ENTITY_BASE/ib_bfm_rdy_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/ib_bfm_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/ib_bfm.vhd"
