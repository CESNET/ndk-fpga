# Modules.tcl: Local include tcl script
# Copyright (C) 2018 CESNET
# Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MATH_PKG  "$OFM_PATH/comp/base/pkg"

set MUX_BASE "$OFM_PATH/comp/base/logic/mux"
set NP_LUTRAM_PRO_BASE "$OFM_PATH/comp/base/mem/np_lutram_pro"

set COMPONENTS [ list \
                  [ list "GEN_MUX"                 $MUX_BASE                "FULL" ] \
                  [ list "NP_LUTRAM_PRO"           $NP_LUTRAM_PRO_BASE      "FULL" ] \
               ]

set PACKAGES "$PACKAGES $MATH_PKG/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/n_loop_op_pro.vhd"
