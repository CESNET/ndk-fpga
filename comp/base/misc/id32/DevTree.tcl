# 1. base - base address on MI bus
proc dts_idcomp {base} {
	set    ret ""
	append ret "idcomp {"
	append ret "compatible = \"netcope,idcomp\";"
	append ret "reg = <$base 256>;"
	append ret "version = <0x00010003>;"
	append ret "};"
	return $ret
}
