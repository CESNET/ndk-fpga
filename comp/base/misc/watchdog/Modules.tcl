# Modules.tcl: Components include script
# Copyright (C) 2015 CESNET
# Author: Adam Piecek <xpiece00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# packages
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# modules
set MOD "$MOD $ENTITY_BASE/watchdog_ent.vhd"
set MOD "$MOD $ENTITY_BASE/watchdog_mi32_ent.vhd"
set MOD "$MOD $ENTITY_BASE/watchdog_mi32_arch.vhd"
set MOD "$MOD $ENTITY_BASE/watchdog_arch.vhd"
