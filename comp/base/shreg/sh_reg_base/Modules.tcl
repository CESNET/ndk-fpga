# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all component

set MOD "$MOD $ENTITY_BASE/sh_reg_base_dynamic_ent.vhd"
set MOD "$MOD $ENTITY_BASE/sh_reg_base_dynamic_arch.vhd"
set MOD "$MOD $ENTITY_BASE/sh_reg_base_static.vhd"


set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
