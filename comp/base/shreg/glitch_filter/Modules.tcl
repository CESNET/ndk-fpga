# Modules.tcl: Local include tcl script
# Copyright (C) 2010 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/glitch_filter.vhd"
