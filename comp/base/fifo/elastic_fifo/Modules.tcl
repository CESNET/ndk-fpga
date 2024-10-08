# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set PKG_BASE                  "$OFM_PATH/comp/base/pkg"
set ASFIFOX_BASE              "$OFM_PATH/comp/base/fifo/asfifox"
set ASYNC_RST_BASE            "$OFM_PATH/comp/base/async/reset"
set MUX_BASE                  "$OFM_PATH/comp/base/logic/mux"
set FIRST_ONE_BASE            "$OFM_PATH/comp/base/logic/first_one"
set ENC_BASE                  "$OFM_PATH/comp/base/logic/enc"
set DEMUX_BASE                "$OFM_PATH/comp/base/logic/demux"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "ASFIFOX"           $ASFIFOX_BASE        "FULL" ] \
   [ list "ASYNC_RESET"       $ASYNC_RST_BASE      "FULL" ] \
   [ list "MUX"               $MUX_BASE            "FULL" ] \
   [ list "FIRST_ONE"         $FIRST_ONE_BASE      "FULL" ] \
   [ list "ENC"               $ENC_BASE            "FULL" ] \
   [ list "DEMUX"             $DEMUX_BASE          "FULL" ]
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/elastic_fifo.vhd"
