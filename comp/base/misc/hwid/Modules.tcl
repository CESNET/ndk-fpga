# Modules.tcl: Local include tcl script
# Copyright (C) 2022 CESNET
# Author: Martin Spinler <spinler@cesnet.cz>

lappend MOD "$ENTITY_BASE/hwid_ent.vhd"

if {$ARCHGRP == "USP"} {
    lappend MOD "$ENTITY_BASE/hwid_usp.vhd"
} else {
    lappend MOD "$ENTITY_BASE/hwid_empty.vhd"
}
