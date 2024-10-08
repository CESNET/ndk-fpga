# 1. no    - tx mac lite numero (id)
# 2. speed - speed of all tx mac lites per port
# 3. base  - base mi address
# 4. mtu   - tx mac lite mtu
proc dts_tx_mac_lite {no speed base mtu} {
	set    size 0x0200
	# set    size 0x01FF
	set    ret ""
	append ret "txmac$no {"
	append ret "compatible = \"netcope,txmac\";"
	append ret "type = \"tx_mac_lite\";"
	append ret "speed = \"$speed\";"
	# how to determine version ?
	append ret "version = <0x00000002>;"
	append ret "reg = <$base $size>;"
	append ret "mtu = <$mtu>;"
	append ret "};"
	return $ret
}
