# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PACKAGES     "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/mfb_frame_cnt.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_frame_cnt_mvb_only.vhd"
