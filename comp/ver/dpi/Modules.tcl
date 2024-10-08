# Modules.tcl: Modules.tcl script to compile the design
# Copyright (C) 2015 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD    "$MOD $ENTITY_BASE/dpi_test.sv"
set SV_LIB "$ENTITY_BASE/dpi_test $SV_LIB"
