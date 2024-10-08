# Modules.tcl: Modules.tcl script to include sources for block_lock.vhd
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PACKAGES  "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/block_lock.vhd"
