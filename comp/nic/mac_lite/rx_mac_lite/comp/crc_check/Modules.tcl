# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set GEN_MUX_BASE       "$OFM_PATH/comp/base/logic/mux"
set SH_REG_BASE        "$OFM_PATH/comp/base/shreg/sh_reg_base"
set CRC_CUTTER_BASE    "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite/comp/crc_cutter"

# This submodule is not open-source.
# Due to licensing reasons, it is not available in the OFM repository.
set MFB_CRC32_ETH_BASE "$OFM_PATH/../modules/fokus/mfb_tools/proc/crc32_ethernet"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/crc_check_ent.vhd"

if { $ARCHGRP == "NO_CRC" } {
   set MOD "$MOD $ENTITY_BASE/crc_check_empty.vhd"
} else {
   set COMPONENTS [list \
      [list "GEN_MUX"             $GEN_MUX_BASE       "FULL" ] \
      [list "MFB_CRC32_ETHERNET"  $MFB_CRC32_ETH_BASE "FULL" ] \
      [list "SH_REG_BASE_STATIC"  $SH_REG_BASE        "FULL" ] \
      [list "GMII_DEC_CRC_CUTTER" $CRC_CUTTER_BASE    "FULL" ] \
   ]

   # Source files for implemented component
   set MOD "$MOD $ENTITY_BASE/get_crc32.vhd"
   set MOD "$MOD $ENTITY_BASE/crc_check.vhd"
}
