# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2008 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

if { $ARCHGRP == "FULL"} {
    set MOD "$MOD $ENTITY_BASE/fl_sampler.vhd"
}
