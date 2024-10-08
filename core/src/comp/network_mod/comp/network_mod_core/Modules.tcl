# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>, Jakub Zahora <xzahor06@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set ASYNC_BASE          "$OFM_PATH/comp/base/async/"
set MGMT_BASE           "$OFM_PATH/comp/nic/eth_phy/comp/mgmt"
set RX_ADAPTER_BASE     "$OFM_PATH/comp/nic/mac_lite/rx_mac_lite/comp/adapters"
set TX_ADAPTER_BASE     "$OFM_PATH/comp/nic/mac_lite/tx_mac_lite/comp/adapters"
set MI_TOOLS_BASE       "$OFM_PATH/comp/mi_tools"
set CARDS_BASE          "$OFM_PATH/../cards"
set DK_1SDX_IP_BASE     "$CARDS_BASE/dk-dev-1sdx-p/src/ip"
set DK_AGI_IP_BASE      "$CARDS_BASE/dk-dev-agi027res/src/ip"
set AGI_FH400G_IP_BASE  "$CARDS_BASE/agi-fh400g/src/ip"
set CMAC_IP_BASE        "$CARDS_BASE/fb4cgg3/src/ip"
set 40GE_BASE           "$OFM_PATH/comp/nic/eth_phy/40ge"
set LL10GE40GE_BASE     "$OFM_PATH/../modules/hft/comp/net_mod/top"
set FIFO_BASE           "$OFM_PATH/comp/base/fifo"
set MI_SPLITTER_BASE    "$OFM_PATH/comp/mi_tools/splitter_plus_gen"
set BASE_LOGIC_BASE     "$OFM_PATH/comp/base/logic"
set TSU_BASE            "$OFM_PATH/comp/tsu"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/eth_hdr_pack.vhd"

# For local synthesis only !
#set ARCHGRP FB4CGG3

lappend COMPONENTS [list "MI_INDIRECT_ACCESS"   "$MI_TOOLS_BASE/indirect_access"   "FULL"]
lappend COMPONENTS [list "MI_SPLITTER_PLUS_GEN" "$MI_TOOLS_BASE/splitter_plus_gen" "FULL"]
lappend COMPONENTS [list "MGMT"                  $MGMT_BASE                        "FULL"]
lappend COMPONENTS [list "TSU_FORMAT_CONV"      "$TSU_BASE/tsu_format_to_ns"       "FULL"]

lappend MOD "$ENTITY_BASE/network_mod_core_ent.vhd"

if { $ARCHGRP == "F_TILE"} {
    lappend COMPONENTS [list "TX_FTILE_ADAPTER"    "$TX_ADAPTER_BASE/mac_seg"                "FULL"]
    lappend COMPONENTS [list "RX_FTILE_ADAPTER"    "$RX_ADAPTER_BASE/mac_seg"                "FULL"]
    lappend COMPONENTS [list "FIFOX"               "$FIFO_BASE/fifox"                        "FULL"]
    lappend COMPONENTS [list "ASYNC_BUS_HANDSHAKE" "$OFM_PATH/comp/base/async/bus_handshake" "FULL"]

    # IP are now in card (400G1) top-level Modules.tcl
    # Uncomment for network module synthesis only!
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_1x400g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_1x400g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_2x200g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_2x200g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_4x100g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_4x100g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_8x50g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_8x50g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_2x40g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_2x40g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_8x25g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_8x25g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_pll_8x10g.ip"
    #lappend MOD "$AGI_FH400G_IP_BASE/ftile_eth_8x10g.ip"

    # IP are now in card (DK-DEV-AGI027RES) top-level Modules.tcl
    # Uncomment for network module synthesis only!
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_1x400g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_1x400g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_2x200g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_2x200g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_4x100g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_4x100g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_8x50g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_8x50g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_2x40g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_2x40g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_8x25g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_8x25g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_pll_8x10g.ip"
    #lappend MOD "$DK_AGI_IP_BASE/ftile_eth_8x10g.ip"

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/ftile_init.vhd"
    lappend MOD "$ENTITY_BASE/macseg_loop.vhd"
    lappend MOD "$ENTITY_BASE/comps/bridge_drp/bridge_drp.vhd"

    # Basic Ftile IP core components
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_1x400g8.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_2x200g4.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_4x100g2.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_2x100g4.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_8x50g1.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_2x40g4.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_8x25g1.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_8x10g1.vhd"
    # Multirate Ftile IP core components
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_multirate_eth_2x100g4.vhd"
    lappend MOD "$ENTITY_BASE/comps/ftile/ftile_multirate_eth_8x25g1_8x10g1.vhd"

    # Verification probe
    lappend MOD "$ENTITY_BASE/comps/ftile_ver_probe/ftile_ver_probe.vhd"

    lappend MOD "$ENTITY_BASE/network_mod_core_ftile.vhd"
}

if { $ARCHGRP == "E_TILE"} {
    lappend COMPONENTS [list "TX_ETILE_ADAPTER"    "$TX_ADAPTER_BASE/avst_100g"               "FULL"]
    lappend COMPONENTS [list "RX_ETILE_ADAPTER"    "$RX_ADAPTER_BASE/eth_avst"                "FULL"]
    lappend COMPONENTS [list "ASYNC_BUS_HANDSHAKE" "$OFM_PATH/comp/base/async/bus_handshake"  "FULL"]
    lappend COMPONENTS [list "FIFOX_MULTI"         "$FIFO_BASE/fifox_multi"                   "FULL"]
    lappend COMPONENTS [list "ASYNC_FIFO"          "$FIFO_BASE/asfifox"                       "FULL"]
    lappend COMPONENTS [list "ASYNC_RESET"         "$ASYNC_BASE/reset"                        "FULL"]
    lappend COMPONENTS [list "MI_SPLITTER"         $MI_SPLITTER_BASE                          "FULL"]
    lappend COMPONENTS [list "EDGE_DETECT"         "$BASE_LOGIC_BASE/edge_detect"             "FULL"]
    lappend COMPONENTS [list "PULSE_EXTEND"        $MGMT_BASE                                 "FULL"]

    # IP are now in card top-level Modules.tcl
    # Uncomment for network module synthesis only!
    #lappend MOD "$DK_1SDX_IP_BASE/etile_eth_1x100g.ip"
    #lappend MOD "$DK_1SDX_IP_BASE/etile_eth_4x25g.ip"
    #lappend MOD "$DK_1SDX_IP_BASE/etile_eth_4x10g.ip"

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/etile_init.vhd"
    lappend MOD "$ENTITY_BASE/avst_loop.vhd"
    lappend MOD "$ENTITY_BASE/ts_demo_logic.vhd"
    lappend MOD "$ENTITY_BASE/network_mod_core_etile.vhd"
}
 
if { $ARCHGRP == "CMAC" } {
    lappend COMPONENTS [list "ASYNC_RESET"     "$ASYNC_BASE/reset"     "FULL"]
    lappend COMPONENTS [list "ASYNC_OPEN_LOOP" "$ASYNC_BASE/open_loop" "FULL"]
    lappend COMPONENTS [list "TX_LBUS_ADAPTER" "$TX_ADAPTER_BASE/lbus" "FULL"]
    lappend COMPONENTS [list "RX_LBUS_ADAPTER" "$RX_ADAPTER_BASE/lbus" "FULL"]

    # IP are now in card top-level Modules.tcl
    # Uncomment for network module synthesis only!
    #lappend MOD "$CMAC_IP_BASE/cmac_eth_1x100g/cmac_eth_1x100g.xci"

    # Source files for implemented component
    lappend MOD "$ENTITY_BASE/network_mod_core_cmac.vhd"

}

if { $ARCHGRP == "40GE" } {
    lappend COMPONENTS [list "ASYNC_RESET"     "$ASYNC_BASE/reset"         "FULL"]
    lappend COMPONENTS [list "ASYNC_OPEN_LOOP" "$ASYNC_BASE/open_loop"     "FULL"]
    lappend COMPONENTS [list "RX_MII_ADAPTER"  "$RX_ADAPTER_BASE/umii_dec" "FULL"]
    lappend COMPONENTS [list "TX_MII_ADAPTER"  "$TX_ADAPTER_BASE/umii_enc" "FULL"]
    lappend COMPONENTS [list "40GE PCS PMA"    "$40GE_BASE"                "FULL"]

    lappend  MOD "$ENTITY_BASE/network_mod_core_40ge.vhd"
}

if { $ARCHGRP == "CESNET_LL10GE" || $ARCHGRP == "CESNET_LL40GE" } {
    if { [file exists "$LL10GE40GE_BASE/Modules.tcl"] == 1} {
        lappend COMPONENTS [list "CESNET_LL10GE40GE" $LL10GE40GE_BASE $ARCHGRP]
        lappend MOD "$LL10GE40GE_BASE/network_mod_core_10ge_40ge_ll.vhd"
    } else {
        puts stderr "ERROR: CESNET LL10GE40GE IP not found. This IP is not publicly available and requires an additional license!"
        exit 1
    }
}
