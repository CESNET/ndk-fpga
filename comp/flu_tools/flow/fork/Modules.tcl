# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE    "$OFM_PATH/comp/base/pkg"

# Entities
set MOD "$MOD $ENTITY_BASE/flu_fork.vhd"

# Wrappers for FL_FORK
set MOD "$MOD $ENTITY_BASE/flu_fork_1to2.vhd"
set MOD "$MOD $ENTITY_BASE/flu_fork_1to3.vhd"
set MOD "$MOD $ENTITY_BASE/flu_fork_1to4.vhd"

# components
set COMPONENTS [list [list "PKG_MATH"        $PKG_BASE       "MATH"]]
