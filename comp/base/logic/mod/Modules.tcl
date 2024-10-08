# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Paths
set MATH_PKG     "$OFM_PATH/comp/base/pkg"

set PACKAGES   "$PACKAGES  $MATH_PKG/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/mod.vhd"
