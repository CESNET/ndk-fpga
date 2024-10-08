# Modules.tcl: Local include tcl script
# Copyright (C) 2018 CESNET
# Author: Petr Panak <xpanak04@stud.feec.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set MOD "$MOD $ENTITY_BASE/../xor96/xor96.vhd"
set MOD "$MOD $ENTITY_BASE/xor_first.vhd"
set MOD "$MOD $ENTITY_BASE/xor_middle.vhd"
set MOD "$MOD $ENTITY_BASE/xor_last.vhd"
set MOD "$MOD $ENTITY_BASE/xor_gen.vhd"
