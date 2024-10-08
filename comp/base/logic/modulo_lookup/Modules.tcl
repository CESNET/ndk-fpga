# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Jan Kučera <xkucer73@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths


# Source files for all components
set MOD "$MOD $ENTITY_BASE/modulo_lookup_ent.vhd"
set MOD "$MOD $ENTITY_BASE/modulo_lookup_full.vhd"

# Set packages
set PACKAGES  "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
