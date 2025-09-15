proc dts_card_specific {base} {
    # Hitek CLV MACs on N5014
    set ADDR_CLV_MAC    "0x01800000"
    set ret ""
    global CLV_MOD_ARCH CLV_PORTS CLV_PORT_SPEED CLV_PORT_CHAN CLV_PORT_LANES CARD_NAME ETH_PORT_TX_MTU ETH_PORT_RX_MTU
    if {$CLV_MOD_ARCH == "HITEK"} {
        append ret [dts_clv_mod $ADDR_CLV_MAC $CLV_PORTS CLV_PORT_SPEED CLV_PORT_CHAN CLV_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU $CLV_MOD_ARCH $CARD_NAME]
    }
    return $ret
}
