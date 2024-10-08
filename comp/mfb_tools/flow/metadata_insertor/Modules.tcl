# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET z. s. p. o.
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SHAKEDOWN_BASE   "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set MVB_FIFOX_BASE   "$OFM_PATH/comp/mvb_tools/storage/fifox"
set FIFOX_MULTI_BASE "$OFM_PATH/comp/base/fifo/fifox_multi"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "SHAKEDOWN"   $SHAKEDOWN_BASE   "FULL" ]
lappend COMPONENTS [ list "MVB_FIFOX"   $MVB_FIFOX_BASE   "FULL" ]
lappend COMPONENTS [ list "FIFOX_MULTI" $FIFOX_MULTI_BASE "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/metadata_insertor.vhd"
