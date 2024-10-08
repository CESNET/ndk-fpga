proc dts_stratix_adc_sensors {base} {
	set ret ""
	append ret "adc_sensors {"
	append ret "reg = <$base 0x7C>;"
	append ret "compatible = \"netcope,stratix_adc_sensors\";"
	append ret "};"
	return $ret
}
