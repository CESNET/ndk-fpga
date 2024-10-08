# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET
# Author(s): Vladislav Valek <xvalek14@vutbr.cz>
#


lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

set BARREL_SHIFTER_BASE       "$OFM_PATH/comp/base/logic/barrel_shifter"

lappend COMPONENTS \
    [list "BARREL_SHIFTER_GEN" $BARREL_SHIFTER_BASE "FULL"] \


lappend MOD "$ENTITY_BASE/mfb_to_lbus_reconf.vhd"
