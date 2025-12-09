# Modules.tcl: Components include script
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Component paths
set MFB_SPLITTER_BASE "$OFM_PATH/comp/mfb_tools/flow/splitter"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MFB_SPLITTER" $MFB_SPLITTER_BASE "FULL" ]

lappend MOD "$ENTITY_BASE/mfb_discarder.vhd"
