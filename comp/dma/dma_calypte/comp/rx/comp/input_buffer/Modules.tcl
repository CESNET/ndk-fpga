# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend MOD "$ENTITY_BASE/rx_dma_calypte_input_buffer.vhd"

lappend COMPONENTS [list "BARREL_SHIFTER_GEN" "$OFM_PATH/comp/base/logic/barrel_shifter" "FULL"]

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
