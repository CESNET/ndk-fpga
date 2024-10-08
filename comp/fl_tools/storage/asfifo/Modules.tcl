# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MATH_PKG_BASE    "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES         "$PACKAGES $MATH_PKG_BASE/math_pack.vhd"

# Entities
set MOD "$MOD $ENTITY_BASE/fl_asfifo_cv2_64b.vhd"
set MOD "$MOD $ENTITY_BASE/fl_asfifo_cv2_16b.vhd"
set MOD "$MOD $ENTITY_BASE/fl_asfifo_cv2_128b.vhd"
set MOD "$MOD $ENTITY_BASE/fl_asfifo_cv2_256b.vhd"

set COMPONENTS [list [list "GEN_OR" $OFM_PATH/comp/base/logic/or "FULL" ]]
