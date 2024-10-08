# Modules.tcl: Modules.tcl script to compile all design
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths
set DEC1FN_ENABLE_BASE "$OFM_PATH/comp/base/logic/dec1fn"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

if { $ARCHGRP == "FULL" } {
  # Components
  lappend COMPONENTS [ list "DEC1FN_ENABLE" $DEC1FN_ENABLE_BASE "FULL" ]

  # Files
  lappend MOD "$ENTITY_BASE/streaming_debug_probe.vhd"
  lappend MOD "$ENTITY_BASE/streaming_debug_probe_n.vhd"
  lappend MOD "$ENTITY_BASE/streaming_debug_probe_mfb.vhd"
  lappend MOD "$ENTITY_BASE/streaming_debug_master.vhd"
  lappend MOD "$ENTITY_BASE/DevTree.tcl"
}

if { $ARCHGRP == "PROBE" } {
  # Files
  lappend MOD "$ENTITY_BASE/streaming_debug_probe.vhd"
  lappend MOD "$ENTITY_BASE/streaming_debug_probe_n.vhd"
  lappend MOD "$ENTITY_BASE/streaming_debug_probe_mfb.vhd"
}
