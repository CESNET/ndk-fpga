# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE  "$OFM_PATH/comp/base/pkg"

set MOD  "$MOD $ENTITY_BASE/dp_uram_xilinx_ent.vhd"
set MOD  "$MOD $ENTITY_BASE/dp_uram_xilinx_arch.vhd"
