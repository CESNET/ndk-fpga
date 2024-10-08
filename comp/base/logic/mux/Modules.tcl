# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for the component


set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/mux.vhd"
set MOD "$MOD $ENTITY_BASE/mux_onehot.vhd"
set MOD "$MOD $ENTITY_BASE/mux_piped.vhd"
set GEN_ENC    "$OFM_PATH/comp/base/logic/enc"

set COMPONENTS [ list \
                  [ list "GEN_ENC"                 $GEN_ENC                 "FULL" ] \
               ]
