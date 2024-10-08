# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE    "$OFM_PATH/comp/base/pkg"


set MOD "$MOD $ENTITY_BASE/mfb_fork.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_fork_1to2.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_fork_1to3.vhd"

# components
set COMPONENTS [list [list "PKG_MATH"        $PKG_BASE       "MATH"]]
