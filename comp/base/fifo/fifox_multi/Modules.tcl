# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set LOCAL_COMP "$ENTITY_BASE/comp/fifox_multi_gen"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI_GEN" $LOCAL_COMP "FULL" ]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/fifox_multi.vhd"
