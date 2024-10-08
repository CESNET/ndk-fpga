# Modules.tcl: Modules.tcl script for component
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Common paths

# Paths to components
set ASYNC_RESET_BASE "$OFM_PATH/comp/base/async/reset"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "ASYNC_RESET" $ASYNC_RESET_BASE "FULL" ] \
]]

# Individual modules
set MOD "$MOD $ENTITY_BASE/reset_tree_gen.vhd"
