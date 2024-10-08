# Modules.tcl: Local include script
# Copyright (C) 2022 CESNET
# Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "UVM_BYTE_ARRAY"   "$OFM_PATH/comp/uvm/byte_array"     "FULL"]
lappend COMPONENTS [list "UVM_MII"          "$OFM_PATH/comp/uvm/mii"            "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
