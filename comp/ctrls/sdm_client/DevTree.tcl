# 1. base - base address on MI bus
proc dts_sdm_controller {base} {
	set    ret ""
	append ret "intel_sdm_controller {"
	append ret "compatible = \"netcope,intel_sdm_controller\";"
	append ret "reg = <$base 44>;"
	append ret "type = <0>;"
	append ret "version = <0x00000001>;"
	append ret "};"
	return $ret
}
