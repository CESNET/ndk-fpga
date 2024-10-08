# Modules.tcl: Local include Modules script
# Copyright (C) 2009 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

  set MOD "$MOD $ENTITY_BASE/i2c_master_bit_ctrl.vhd"
  set MOD "$MOD $ENTITY_BASE/i2c_master_byte_ctrl.vhd"
  set MOD "$MOD $ENTITY_BASE/i2c_master_top.vhd"
  set MOD "$MOD $ENTITY_BASE/i2c_op.vhd"

set MOD "$MOD $ENTITY_BASE/DevTree.tcl"
