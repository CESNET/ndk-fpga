# Modules.tcl: Local include script
# Copyright (C) 2022 CESNET
# Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "COMMON"       "$OFM_PATH/comp/uvm/common"         "FULL"]

lappend MOD "$ENTITY_BASE/pkg.sv"
lappend MOD "$ENTITY_BASE/interface.sv"
