# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause
#

# Base directories
set FL_BASE             "$OFM_PATH/comp/fl_tools"

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd \
                        $FL_BASE/pkg/fl_pkg.vhd         \
                        $OFM_PATH/comp/mi_tools/pkg/mi32_pkg.vhd"


set MOD "$MOD $ENTITY_BASE/monitor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/monitor_arch_full.vhd"
set MOD "$MOD $ENTITY_BASE/top/monitor_top1.vhd"
set MOD "$MOD $ENTITY_BASE/top/monitor_top4.vhd"
