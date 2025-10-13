# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2022 CESNET
# Author: David Beneš <benes@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Files
lappend MOD "$ENTITY_BASE/bmc_driver.vhd"

