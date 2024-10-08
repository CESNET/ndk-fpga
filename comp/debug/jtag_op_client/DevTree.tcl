# maximum JTAG-over-protocol IP memory size is 0x4000 (x3 constituent parts)
proc dts_jtag_op_controller {base} {
	set    ret ""
	append ret "intel_jtag_op_controller {"
	append ret "compatible = \"cesnet,ofm,intel_jtag_op_ctrl\";"
	append ret "reg = <$base 0xc000>;"
	append ret "type = <0>;"
	append ret "version = <0x00000001>;"
	append ret "};"
	return $ret
}
