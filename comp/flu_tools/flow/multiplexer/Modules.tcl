# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2012 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MUX_BASE    "$OFM_PATH/comp/base/logic/mux"
set DEMUX_BASE  "$OFM_PATH/comp/base/logic/demux"
set PKG_BASE    "$OFM_PATH/comp/base/pkg"

# Entities
set MOD "$MOD $ENTITY_BASE/flu_multiplexer.vhd"
set MOD "$MOD $ENTITY_BASE/flu_multiplexer_packet.vhd"
set MOD "$MOD $ENTITY_BASE/flu_multiplexer_dpacket.vhd"
set MOD "$MOD $ENTITY_BASE/flu_plus_multiplexer.vhd"
set MOD "$MOD $ENTITY_BASE/flu_plus_multiplexer_packet.vhd"

# components
set COMPONENTS [list [list "PKG_MATH"        $PKG_BASE       "MATH"]\
                     [list "MUX"             $MUX_BASE       "FULL"]\
                     [list "DEMUX"           $DEMUX_BASE     "FULL"]]
