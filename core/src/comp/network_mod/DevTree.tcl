# 1.  base_mac        - base address of MAC layer
# 2.  base_pcs        - base address of PCS/PMA layer
# 3.  base_pmd        - base address of PMD/I2C layer
# 4.  ports           - number of ethernet ports
# 5.  ETH_PORT_SPEED  - array of integer, speed value for all ports
# 6.  ETH_PORT_CHAN   - array of integer, number of channels for all ports
# 7.  ETH_PORT_LANES  - array of integer, number of lanes for all ports
# 8.  ETH_PORT_RX_MTU - array of integer, RX MTU value for all ports
# 9.  ETH_PORT_TX_MTU - array of integer, TX MTU value for all ports
# 10. eth_ip_name     - name of used IP (CMAC, E-Tile,...)
# 11. qsfp_cages      - number of QSFP cages
# 12. QSFP_I2C_ADDR   - array of integer, I2C address for all QSFP cages
# 13. card_name       - name of the card
proc dts_network_mod { base_mac base_pcs base_pmd ports ETH_PORT_SPEED ETH_PORT_CHAN ETH_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU eth_ip_name qsfp_cages QSFP_I2C_ADDR card_name} {

    # use upvar to pass an array
    upvar $ETH_PORT_SPEED port_speed
    upvar $ETH_PORT_CHAN  port_chan
    upvar $ETH_PORT_LANES port_lanes
    upvar $ETH_PORT_RX_MTU port_rx_mtu
    upvar $ETH_PORT_TX_MTU port_tx_mtu
    upvar $QSFP_I2C_ADDR pmd_i2c_addr

    set ei 0
    # MAC Lites offset (9 bits)
    set TX_RX_MAC_OFF  0x0200
    # MAC Lites offset for channels (MAC Lites offset + 1 extra bit)
    set CHAN_OFF       0x0400
    # MAC Lites offset for ports (MAC Lites offset for channels + 3 extra bits)
    set PORTS_OFF      0x2000
    # Port offset of MGMT PCS registers
    set MGMT_PORT_OFF  0x200000
    # Chan offset of MGMT PCS registers
    set MGMT_CHAN_OFF  0x40000
    # Port offset of PMD registers
    set PMD_PORT_OFF   0x100

    set I2C_ADDR       0x800010

    set ret ""

    for {set p 0} {$p < $qsfp_cages} {incr p} {
        append ret "i2c$p:" [dts_i2c $p [expr $base_pmd + $PMD_PORT_OFF * $p + 0x10]]
        append ret "pmdctrl$p:" [dts_pmd_ctrl $p [expr $base_pmd + $PMD_PORT_OFF * $p + 0x1c]]
        append ret "pmd$p:" [dts_eth_transciever $p "QSFP" "pmdctrl$p" "i2c$p" $pmd_i2c_addr($p)]
    }

    set ports_per_qsfp [expr $ports / $qsfp_cages]
    global ETH_MAC_BYPASS TS_DEMO_EN

    for {set p 0} {$p < $ports} {incr p} {
        set channel_lanes [expr $port_lanes($p)/$port_chan($p)]
        set pcspma_params "ip-name = \"$eth_ip_name\";"
        set pmd_id [expr $p / $ports_per_qsfp]
        for {set ch 0} {$ch < $port_chan($p)} {incr ch} {
            set    eth_lanes ""
            for {set lan 0} {$lan < $channel_lanes} {incr lan} {
                append eth_lanes "[expr $ch * $channel_lanes + $lan] "
            }
            append ret "regarr$ei:" [dts_pcs_regs $ei [expr $base_pcs + $MGMT_PORT_OFF * $p + $MGMT_CHAN_OFF * $ch]]
            append ret "pcspma$ei:" [dts_mgmt $ei "$port_speed($p)G" "regarr$ei" $pcspma_params]
            if {$ETH_MAC_BYPASS} {
                append ret [dts_eth_channel $ei $pmd_id -1 -1 $ei $eth_lanes]
            } else {
                append ret "txmac$ei:" [dts_tx_mac_lite $ei $port_speed($p) [expr $base_mac + $p * $PORTS_OFF + $ch * $CHAN_OFF + $TX_RX_MAC_OFF * 0] $port_tx_mtu($p)]
                append ret "rxmac$ei:" [dts_rx_mac_lite $ei $port_speed($p) [expr $base_mac + $p * $PORTS_OFF + $ch * $CHAN_OFF + $TX_RX_MAC_OFF * 1] $port_rx_mtu($p)]
                append ret [dts_eth_channel $ei $pmd_id $ei $ei $ei $eth_lanes]
            }
            incr ei
        }
        # For the demo/testing logic in the Network Mod Core (E-Tile)
        if {$TS_DEMO_EN} {
            append ret [dts_ts_demo_logic $p [expr $base_pcs + $MGMT_PORT_OFF * $p + $MGMT_CHAN_OFF]]
        }
    }

    return $ret
}

# 1. no            - node index
# 2. type          - QSFP,...
# 3. pmd_ctrl      - name of PMD control register node
# 4. i2c_ctrl      - name of I2C control module node
# 5. qsfp_i2c_addr - PMD I2C address
proc dts_eth_transciever {no type pmd_ctrl i2c_ctrl qsfp_i2c_addr} {
    set    ret ""
    append ret "pmd$no {"
    append ret "compatible = \"netcope,transceiver\";"
    append ret "type = \"$type\";"
    append ret "status-reg = <&$pmd_ctrl>;"
    append ret "control = <&$i2c_ctrl>;"
    append ret "control-param{i2c-addr=<$qsfp_i2c_addr>;};"
    append ret "};"
    return $ret
}

# 1. no   - node index
# 2. base - base address
proc dts_pmd_ctrl {no base} {
    set ret ""
    append ret "pmdctrl$no {"
    append ret "reg = <$base 4>;"
    append ret "version = <0x00010000>;"
    append ret "};"
    return $ret;
}

# 1. no        - node index
# 2. pmd       - number of transciever used by channel
# 3. rxmac_num - number of rxmac used by channel
# 4. txmac_num - number of txmac used by channel
# 5. phy_num   - number of PCS/PMA used by channel
# 6. lines     - indexes of serial lines used by channel
proc dts_eth_channel {no pmd rxmac_num txmac_num phy_num lines} {
    set    ret ""
    append ret "eth$no {"
    append ret "compatible = \"netcope,eth\";"
    append ret "pmd = <&pmd$pmd>;"
    if {$phy_num   != -1} {append ret "pcspma = <&pcspma$phy_num>;"}
    if {$rxmac_num != -1} {append ret "rxmac = <&rxmac$rxmac_num>;"}
    if {$txmac_num != -1} {append ret "txmac = <&txmac$txmac_num>;"}
    append ret "pmd-params {lines = <$lines>;};"
    append ret "};"
    return $ret;
}

# 1. no        - node index
# 2. base      - base address
proc dts_ts_demo_logic {no base} {
    set    ret ""
    set    packets_regs 0x2
    set    ts_diffs_regs 0x2
    set    ts_min_regs 0x2
    set    ts_max_regs 0x2
    append ret "ts_demo_logic$no {"
    append ret "compatible = \"cesnet,replicator,demo\";"
    append ret "reg = <$base 0x100>;"
    append ret "reset_reg = <0x0 0x1>;"
    append ret "sample_reg = <0x4 0x1>;"
    append ret "packets_reg = <[expr   2                                           *0x4] $packets_regs>;"
    append ret "ts_diffs_reg = <[expr (2+$packets_regs)                            *0x4] $ts_diffs_regs>;"
    append ret "ts_min_reg = <[expr   (2+$packets_regs+$ts_diffs_regs)             *0x4] $ts_min_regs>;"
    append ret "ts_max_reg = <[expr   (2+$packets_regs+$ts_diffs_regs+$ts_min_regs)*0x4] $ts_max_regs>;"
    append ret "};"
    return $ret;
}
