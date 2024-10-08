# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2022 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Files
lappend MOD "$ENTITY_BASE/spi_flash_driver.vhd"