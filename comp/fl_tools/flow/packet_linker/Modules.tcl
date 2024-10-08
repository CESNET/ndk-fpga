# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set FL_BASE       "$ENTITY_BASE/../.."
set FIFO_BASE     "$FL_BASE/storage/fifo"

# Entities
set MOD "$MOD $ENTITY_BASE/packet_linker_ent.vhd"
set MOD "$MOD $ENTITY_BASE/packet_linker_arch.vhd"

# components
set COMPONENTS [list [list "PKG_MATH"        $OFM_PATH/comp/base/pkg       "MATH"]]
