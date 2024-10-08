# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set DP_URAM_BASE "$OFM_PATH/comp/base/mem/dp_uram_xilinx"

set COMPONENTS [list [list "DP_URAM_XILINX" $DP_URAM_BASE "FULL"]]

set MOD  "$MOD $ENTITY_BASE/sdp_uram_xilinx_ent.vhd"
set MOD  "$MOD $ENTITY_BASE/sdp_uram_xilinx_arch.vhd"
