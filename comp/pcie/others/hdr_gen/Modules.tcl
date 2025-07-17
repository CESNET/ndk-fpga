# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for implemented component

lappend COMPONENTS [list "RQ_HDR_GEN"       $ENTITY_BASE/rq_hdr_gen "FULL"]
lappend COMPONENTS [list "CC_HDR_GEN"       $ENTITY_BASE/cc_hdr_gen "FULL"]
lappend COMPONENTS [list "CQ_HDR_DEPARSER"  $ENTITY_BASE/cq_hdr_deparser "FULL"]
lappend COMPONENTS [list "RC_HDR_DEPARSER"  $ENTITY_BASE/rc_hdr_deparser "FULL"]
