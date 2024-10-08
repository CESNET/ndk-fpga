# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend MOD "$ENTITY_BASE/reg_fifo.vhd"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
