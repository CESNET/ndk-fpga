# Modules.tcl: Local include tcl script
# Copyright (C) 2017 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set MOD "$MOD $ENTITY_BASE/fifo_n1_ent.vhd"
set MOD "$MOD $ENTITY_BASE/fifo_n1.vhd"

set MUX_BASE "$OFM_PATH/comp/base/logic/mux"
set PIPE_BASE "$OFM_PATH/comp/base/misc/pipe"
set SDP_DISTMEM_BASE "$OFM_PATH/comp/base/mem/gen_lutram/compatibility"
set N_ONE_BASE "$OFM_PATH/comp/base/logic/n_one"
set BARREL_SHIFTER_BASE "$OFM_PATH/comp/base/logic/barrel_shifter"


set COMPONENTS [ list \
                  [ list "GEN_MUX"                 $MUX_BASE                 "FULL" ] \
                  [ list "GEN_MUX_ONEHOT"                 $MUX_BASE                 "FULL" ] \
                  [ list "PIPE"                 $PIPE_BASE                 "FULL" ] \
                  [ list "SDP_DISTMEM"                 $SDP_DISTMEM_BASE                 "behavioral" ] \
                  [ list "N_ONE"                 $N_ONE_BASE                 "FULL" ] \
                  [ list "BARREL_SHIFTER_GEN"                 $BARREL_SHIFTER_BASE                 "FULL" ] \
               ]

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
set PACKAGES "$PACKAGES $MATH_PKG/type_pack.vhd"
