# Modules.tcl: Local include Modules script
# Copyright (C) 2010 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components


  set PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

  set GF_BASE "$OFM_PATH/comp/base/shreg/glitch_filter"

  set COMPONENTS [list [list GLITCH_FILTER $GF_BASE "FULL" ]]

  set MOD "$MOD $ENTITY_BASE/i2c_slave_bit_ctrl.vhd"
  set MOD "$MOD $ENTITY_BASE/i2c_slave_byte_ctrl.vhd"
  set MOD "$MOD $ENTITY_BASE/i2c_slave_top.vhd"

