#!/bin/bash
#
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# configuration
cable_index=1 # use jtagconfig command for check cable index
quartus_path="/home/jakubcabal/intelFPGA_pro/19.3/qprogrammer/quartus/bin/"

if [ $# != 1 ] ; then
    echo "Usage:"
    echo "------"
    echo "    sh write_pof.sh <input pof file>"
    echo " "
    echo "Example:"
    echo "    sh write_pof.sh my_firmware.pof"
    exit
fi

file=$1
filename=${file%.*}
extension=${file##*.}

if [ $extension != "pof" ] ; then
    echo "Only .pof file is allowed!"
    exit
fi

touch ${filename}".cdf"

if [ $extension == "pof" ] ; then
    echo "/* Quartus Prime Version 19.3.0 Build 222 09/23/2019 Patches 0.01 SC Pro Edition */
JedecChain;
	FileRevision(JESD32A);
	DefaultMfr(6E);

	P ActionCode(Ign)
		Device PartName(10M50DAF256) MfrSpec(OpMask(0) SEC_Device(QSPI_2GB) Child_OpMask(3 0 3 3) PFLPath(\"$file\"));
	P ActionCode(Ign)
		Device PartName(1SD280PT2S1) MfrSpec(OpMask(0));

ChainEnd;

AlteraBegin;
	ChainType(JTAG);
AlteraEnd;" > ${filename}".cdf"

    quartus_pgm -c ${cable_index} ${filename}.cdf
    rm ${filename}.cdf
    echo "Programming Successful!"
fi
