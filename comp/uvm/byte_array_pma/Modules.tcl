# Modules.tcl: Local include script
# Copyright (C) 2021 CESNET
# Author: Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS \
    [list "BYTE_ARRAY" "$OFM_PATH/comp/uvm/byte_array" "FULL"] \
    [list "PMA"        "$OFM_PATH/comp/uvm/pma"        "FULL"] \

lappend MOD "$ENTITY_BASE/pkg.sv"
