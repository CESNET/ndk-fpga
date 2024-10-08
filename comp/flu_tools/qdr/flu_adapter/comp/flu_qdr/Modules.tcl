# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2014 CESNET
# Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Paths
set MATH_PKG     "$OFM_PATH/comp/base/pkg"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/flu_qdr_ent.vhd"


# Setup architecture
set MOD "$MOD $ENTITY_BASE/flu_qdr_arch.vhd"

# Components
set COMPONENTS [list \
      [list "FLU_ADAPTER" $OFM_PATH/comp/flu_tools/qdr/flu_adapter "FULL"] \
      [list "QDR_BRAM" $OFM_PATH/comp/flu_tools/qdr/flu_adapter/comp/qdr_bram "FULL"]
]
