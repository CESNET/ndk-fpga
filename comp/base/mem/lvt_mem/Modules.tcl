# Modules.tcl: Include components for lvt_mem.vhd
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set GEN_REG_ARRAY_BASE  "$OFM_PATH/comp/base/mem/gen_reg_array"
set GEN_LUTRAM_BASE     "$OFM_PATH/comp/base/mem/gen_lutram"
set GEN_LUTRAM_BASE     "$OFM_PATH/comp/base/mem/sdp_bram"
set GEN_MUX_BASE        "$OFM_PATH/comp/base/logic/mux"

lappend PACKAGES  "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"

lappend COMPONENTS  [list   "GEN_REG_ARRAY"     $GEN_REG_ARRAY_BASE     "FULL"]
lappend COMPONENTS  [list   "GEN_LUTRAM"        $GEN_LUTRAM_BASE        "FULL"]
lappend COMPONENTS  [list   "GEN_MUX"           $GEN_MUX_BASE           "FULL"]

lappend MOD "$ENTITY_BASE/lvt_mem.vhd"
