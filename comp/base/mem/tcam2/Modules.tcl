# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2020 CESNET
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
set COMPONENTS [list \
    [ list "DEC1FN"         "$OFM_PATH/comp/base/logic/dec1fn"        "FULL" ] \
    [ list "GEN_LUTRAM"     "$OFM_PATH/comp/base/mem/gen_lutram"      "FULL" ] \
    [ list "SDP_BRAM_BEHAV" "$OFM_PATH/comp/base/mem/sdp_bram"        "FULL" ] \
    [ list "ENC_ENT"        "$OFM_PATH/comp/base/logic/enc"           "FULL" ] \
]

# Source file for tcam component
set MOD "$MOD $ENTITY_BASE/tcam2.vhd"
