# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MUX        "$OFM_PATH/comp/base/logic/mux"
set DEMUX      "$OFM_PATH/comp/base/logic/demux"
set PIPE       "$OFM_PATH/comp/base/misc/pipe"
set FLU_PIPE   "$OFM_PATH/comp/flu_tools/flow/pipe"

set COMPONENTS [ list \
                  [ list "GEN_MUX"              $MUX                  "FULL" ] \
                  [ list "GEN_DEMUX"            $DEMUX                "FULL" ] \
                  [ list "PIPE"                 $PIPE                 "FULL" ] \
                  [ list "FLU_PIPE"             $FLU_PIPE             "FULL" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/comp/mac_replace.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mac_dst_replace.vhd"
set MOD "$MOD $ENTITY_BASE/comp/mac_src_replace.vhd"
set MOD "$MOD $ENTITY_BASE/mac_editor_top_ent.vhd"
set MOD "$MOD $ENTITY_BASE/mac_editor_top_arch.vhd"
