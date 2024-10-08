proc dts_frame_unpacker {unpack_limit} {
	set    ret ""
	append ret "frame_unpacker {"
	append ret "compatible = \"cesnet,ofm,frame_unpacker\";"
	append ret "version = <0x00000001>;"
	append ret "unpack_limit = <$unpack_limit>;"
	append ret "};"
	return $ret
}
