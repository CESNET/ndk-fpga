# my_component.vhd: Description of my component.
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


# Set paths

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set DEC1FN2B_BASE      "$OFM_PATH/comp/base/logic/dec1fn"
set MFB_PIPE_BASE      "$OFM_PATH/comp/mfb_tools/flow/pipe"
set PACP_BASE          "$OFM_PATH/comp/base/misc/packet_planner"
set ONES_INSERTOR_BASE "$OFM_PATH/comp/base/logic/ones_insertor"

set COMPONENTS [list \
	[list "dec1fn2b"         $DEC1FN2B_BASE      "FULL" ]\
	[list "MFB_PIPE"         $MFB_PIPE_BASE      "FULL" ]\
	[list "PACKET_PLANNER"   $PACP_BASE          "FULL" ]\
	[list "ONES_INSERTOR"    $ONES_INSERTOR_BASE "FULL" ]\
]

set MOD "$MOD $ENTITY_BASE/mfb_generator_core.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_generator_core_pacp.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_generator.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_generator_mi32.vhd"
set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
