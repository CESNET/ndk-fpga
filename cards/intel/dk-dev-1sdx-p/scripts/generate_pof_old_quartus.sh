#!/bin/bash
#
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

if [ $# != 1 ] ; then
	echo "Usage:"
	echo "------"
	echo "    sh generate_pof.sh <input sof file>"
	echo " "
	echo "Example:"
	echo "    sh generate_pof.sh my_firmware.sof"
	exit
fi

file=$1
filename=${file%.*}
extension=${file##*.}

if [ $extension != "sof" ] ; then
	echo "Usage:"
	echo "------"
	echo "    sh generate_pof.sh <input sof file>"
	exit
fi

touch ${filename}".cof"

if [ $extension == "sof" ] ; then
	echo "<?xml version=\"1.0\" encoding=\"US-ASCII\" standalone=\"yes\"?>
<cof>
	<eprom_name>CFI_2GB</eprom_name>
	<output_filename>./"${filename}".pof</output_filename>
	<n_pages>1</n_pages>
	<width>1</width>
	<mode>20</mode>
	<sof_data>
		<start_address>00100000</start_address>
		<user_name>Page_0</user_name>
		<page_flags>1</page_flags>
		<bit0>
			<sof_filename>./"${file}"</sof_filename>
		</bit0>
	</sof_data>
	<version>10</version>
	<create_cvp_file>0</create_cvp_file>
	<create_hps_iocsr>0</create_hps_iocsr>
	<auto_create_rpd>0</auto_create_rpd>
	<rpd_little_endian>1</rpd_little_endian>
	<options>
		<map_file>1</map_file>
		<option_start_address>10000</option_start_address>
		<dynamic_compression>0</dynamic_compression>
	</options>
	<advanced_options>
		<ignore_epcs_id_check>1</ignore_epcs_id_check>
		<ignore_condone_check>2</ignore_condone_check>
		<plc_adjustment>0</plc_adjustment>
		<post_chain_bitstream_pad_bytes>-1</post_chain_bitstream_pad_bytes>
		<post_device_bitstream_pad_bytes>-1</post_device_bitstream_pad_bytes>
		<bitslice_pre_padding>1</bitslice_pre_padding>
	</advanced_options>
</cof>" > ${filename}".cof"

	echo "Converting to Programmer Object File."
	quartus_cpf -c ${filename}.cof
	rm ${filename}.cof
fi

echo "POF file generated successfully!"
