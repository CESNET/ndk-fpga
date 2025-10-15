# Modules-tcl: Components include script
# Copyright (C) DynaNIC Semiconductors, Ltd. - All Rights Reserved
# Author: Tomas Fukac <fukac@dyna-nic.com>, 2024
#
# SPDX-License-Identifier: BSD-3-Clause

# Files
lappend MOD "$ENTITY_BASE/fim_dup_tree.sv"
lappend MOD "$ENTITY_BASE/fim_resync.sv"
lappend MOD "$ENTITY_BASE/ofs_std_synchronizer_nocut.sv"
lappend MOD "$ENTITY_BASE/hbm_reset.vhd"

