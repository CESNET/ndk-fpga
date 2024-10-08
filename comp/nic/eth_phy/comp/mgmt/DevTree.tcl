# 1. no      - node index
# 2. type    - 10G, 25G, 40G, 100G, 400G,...
# 3. control - controller unit name for configuration access
# 4. param   - parameter for controller - DTS text properties
proc dts_mgmt {no type control param} {
	set    ret ""
	append ret "pcspma$no {"
	append ret "type = \"$type\";"
	append ret "control = <&$control>;"
	append ret "control-param {" $param "};"
	append ret "};"
	return $ret
}

# 1. no   - node index
# 2. base - base address for MI access of PCS regarray
proc dts_pcs_regs {no base} {
    set   size 0x40000
    set    ret ""
    append ret "regarr$no {"
    append ret "compatible = \"netcope,pcsregs\";"
    append ret "reg = <$base $size>;"
    append ret "};"
    return $ret
}

