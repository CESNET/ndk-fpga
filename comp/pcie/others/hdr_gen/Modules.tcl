# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for implemented component
lappend MOD "$ENTITY_BASE/rq_hdr_gen/rq_hdr_gen.vhd"
lappend MOD "$ENTITY_BASE/cc_hdr_gen/cc_hdr_gen.vhd"
lappend MOD "$ENTITY_BASE/cq_hdr_deparser/cq_hdr_deparser.vhd"
lappend MOD "$ENTITY_BASE/rc_hdr_deparser/rc_hdr_deparser.vhd"
