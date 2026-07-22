# Modules.tcl: Components include script
# Copyright (C) 2026 Dynanic Semiconductors Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Component paths

set MVB_COMP_BASE $OFM_PATH/comp/mvb_tools

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "MVB_SERIALIZER" "$MVB_COMP_BASE/flow/serializer"  "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/mvb2axis.vhd"
