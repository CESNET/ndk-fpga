# Modules.tcl: Modules.tcl script to compile the design
# Copyright (C) 2016 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MOD    "$MOD $ENTITY_BASE/dpi_pcre.sv"
set SV_LIB "$ENTITY_BASE/dpi_pcre $SV_LIB"
