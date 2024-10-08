# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/pcie_mfb2avst.vhd"
