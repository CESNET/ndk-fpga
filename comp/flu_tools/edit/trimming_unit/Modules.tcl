# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories

set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/data_shifter.vhd"
set MOD "$MOD $ENTITY_BASE/trimming_unit_flu_ent.vhd"
set MOD "$MOD $ENTITY_BASE/trimming_unit_flu.vhd"
