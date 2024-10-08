# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2020 CESNET
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause
# packages:
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# modules:
set MOD "$MOD $ENTITY_BASE/transformer_down.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_up.vhd"
set MOD "$MOD $ENTITY_BASE/transformer.vhd"

# components:
set COMPONENTS [list\
	[list "GEN_MUX"			"$OFM_PATH/comp/base/logic/mux"		"FULL"]\
	[list "BARREL_SHIFTER_GEN" 	"$OFM_PATH/comp/base/logic/barrel_shifter"	"FULL"]\
]
