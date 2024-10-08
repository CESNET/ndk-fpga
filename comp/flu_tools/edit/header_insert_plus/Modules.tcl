# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Paths
set HINS_BASE  "$OFM_PATH/comp/flu_tools/edit/header_insert"

# Entity
set MOD "$MOD $ENTITY_BASE/hins_plus_ent.vhd"

# Full architecture
if { $ARCHGRP == "FULL" } {

   set COMPONENTS [list \
      [ list "HINS" $HINS_BASE "FULL" ]  \
   ]

   set MOD "$MOD $ENTITY_BASE/hins_plus.vhd"
}

# Empty architecture
if { $ARCHGRP == "EMPTY" } {

   set COMPONENTS [list \
      [ list "HINS" $HINS_BASE "EMPTY" ]  \
   ]

   set MOD "$MOD $ENTITY_BASE/hins_plus_empty.vhd"
}
