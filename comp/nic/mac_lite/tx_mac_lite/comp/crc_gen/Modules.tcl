# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"

# This submodule is not open-source.
# Due to licensing reasons, it is not available in the OFM repository.
set MFB_CRC32_ETH_BASE "$OFM_PATH/../modules/fokus/mfb_tools/proc/crc32_ethernet"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/crc_gen_ent.vhd"

if { $ARCHGRP == "NO_CRC" } {
   set MOD "$MOD $ENTITY_BASE/crc_gen_empty.vhd"
} else {
   set COMPONENTS [list \
      [list "MFB_CRC32_ETHERNET"  $MFB_CRC32_ETH_BASE "FULL" ] \
   ]

   # Source files for implemented component
   set MOD "$MOD $ENTITY_BASE/crc_gen.vhd"
}
