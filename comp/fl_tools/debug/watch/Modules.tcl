# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Viktor Pus <pus@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"
set MUX_BASE "$OFM_PATH/comp/base/logic/mux"

set PACKAGES "$PACKAGES $OFM_PATH/comp/mi_tools/pkg/mi32_pkg.vhd"

set COMPONENTS [list [list "PKG" $PKG_BASE "MATH" ] \
                     [list "MUX" $MUX_BASE "FULL" ] \
               ]

set MOD "$MOD $ENTITY_BASE/watch_ent.vhd"
set MOD "$MOD $ENTITY_BASE/watch_extended_ent.vhd"
set MOD "$MOD $ENTITY_BASE/watch_ent_norec.vhd"
set MOD "$MOD $ENTITY_BASE/watch_extended_ent_norec.vhd"

if {$ARCHGRP == "FULL"} {
   set MOD "$MOD $ENTITY_BASE/guard.vhd"
   set MOD "$MOD $ENTITY_BASE/watch_arch.vhd"

   set MOD "$MOD $ENTITY_BASE/guard_extended.vhd"
   set MOD "$MOD $ENTITY_BASE/watch_extended_arch.vhd"

   set MOD "$MOD $ENTITY_BASE/watch_arch_norec.vhd"
   set MOD "$MOD $ENTITY_BASE/watch_extended_arch_norec.vhd"

   set MOD "$MOD $ENTITY_BASE/synth/fl_watch_2.vhd"
   set MOD "$MOD $ENTITY_BASE/synth/fl_watch_2_hdr.vhd"
   set MOD "$MOD $ENTITY_BASE/synth/fl_watch_4.vhd"
   set MOD "$MOD $ENTITY_BASE/synth/fl_watch_4_hdr.vhd"
}

if {$ARCHGRP == "EMPTY"} {
   set MOD "$MOD $ENTITY_BASE/watch_arch_empty.vhd"
   set MOD "$MOD $ENTITY_BASE/watch_arch_norec_empty.vhd"
}

if {$ARCHGRP == "FULL_LB"} {
    set LB  "FULL"
    set LB_BASE "$COMP_BASE/old/lb"

    set LB_COMP [list [list "LOCAL_BUS" $LB_BASE    $LB]]

    set COMPONENTS "$COMPONENTS $LB_COMP"

    set MOD "$MOD $ENTITY_BASE/watch_lb.vhd"
    set MOD "$MOD $ENTITY_BASE/watch_lb_norec.vhd"
}
