# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2014 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories
set FLU_BASE            "$OFM_PATH/comp/flu_tools"

# Package list
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Component base
set FLU_MUX_BASE        "$FLU_BASE/flow/multiplexer"
set FLU_PIPE_BASE       "$FLU_BASE/flow/pipe"
set FLU_MUX_DSP_BASE    "$ENTITY_BASE/../flu_multiplexer_dsp"
set OR_BASE             "$OFM_PATH/comp/base/logic/or"
set MUX_BASE            "$OFM_PATH/comp/base/logic/mux"
set MUX_DSP_BASE        "$OFM_PATH/comp/base/logic/mux"


# Component list
set COMPONENTS [list \
         [list "FLU_MUX"         $FLU_MUX_BASE           "FULL"  ] \
         [list "FLU_PIPE"        $FLU_PIPE_BASE          "FULL"  ] \
         [list "OR"              $OR_BASE                "FULL"  ] \
         [list "MUX"             $MUX_BASE               "FULL"  ] \
]

# Include some Xilinx specific components
if { "$ARCHGRP" == "" || "$ARCHGRP" == "FULL" } {
    set COMPONENTS [concat $COMPONENTS [list \
        [list "MUX_DSP"         $MUX_DSP_BASE           "FULL"  ] \
        [list "FLU_MUX_DSP"     $FLU_MUX_DSP_BASE         ] \
    ]]
}

# RR select entity and architecture
set MOD "$MOD $ENTITY_BASE/rr_select_ent.vhd"
set MOD "$MOD $ENTITY_BASE/rr_select_arch.vhd"
