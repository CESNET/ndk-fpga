# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET z. s. p. o.
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SHAKEDOWN_BASE   "$OFM_PATH/comp/mvb_tools/flow/shakedown"
set MVB_PIPE_BASE    "$OFM_PATH/comp/mvb_tools/flow/pipe"
set MFB_PIPE_BASE    "$OFM_PATH/comp/mfb_tools/flow/pipe"

set PKG_BASE         "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

# list of sub-components
set COMPONENTS [ list \
    [ list "SHAKEDOWN"   $SHAKEDOWN_BASE   "FULL" ] \
    [ list "MVB_PIPE"    $MVB_PIPE_BASE    "FULL" ] \
    [ list "MFB_PIPE"    $MFB_PIPE_BASE    "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/metadata_extractor.vhd"
