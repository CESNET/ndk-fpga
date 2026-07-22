# Modules.tcl: Components include script
# Copyright (C) 2026 Dynanic Semiconductors Ltd.
# Author(s): David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Files
lappend MOD "$ENTITY_BASE/mvb_serializer.vhd"
