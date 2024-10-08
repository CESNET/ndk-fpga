# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set FL_BASE          "$ENTITY_BASE/../.."

# Packages
set PACKAGES "$FL_BASE/pkg/fl_pkg.vhd"

# Source files for the component
set MOD "$MOD $ENTITY_BASE/trimmer_ent.vhd"
set MOD "$MOD $ENTITY_BASE/trimmer.vhd"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $OFM_PATH/comp/base/pkg     "MATH"] \
   [ list "FL_DEC"      $FL_BASE/misc/decoder    "FULL"] \
]
