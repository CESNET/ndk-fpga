# 1. base - address on MI bus
proc dts_flu_generator {base} {
	set    ret ""
	append ret "flu_generator@$base {"
	append ret "reg = <$base 0x8>;"
	append ret "version = <0x00010001>;"
	append ret "};"
	return $ret
}
