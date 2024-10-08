# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/pipe_tree_adder.vhd"
