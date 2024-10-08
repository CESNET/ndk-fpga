#!/bin/bash
#
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# configuration
cable_index=1 # use jtagconfig command for check cable index

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

if [ $extension == "pof" ] ; then
    touch ${filename}".cdf"
    echo "/* Quartus Prime Version 21.2.0 Build 72 06/14/2021 SC Pro Edition */
JedecChain;
    FileRevision(JESD32A);
    DefaultMfr(6E);

    P ActionCode(Ign)
        Device PartName(AGIB027R29AR0) MfrSpec(OpMask(0));
    P ActionCode(Ign)
        Device PartName(10M50DAF256) MfrSpec(OpMask(0) SEC_Device(QSPI_2GB) Child_OpMask(3 1 1 1) PFLPath(\"$file\"));

ChainEnd;

AlteraBegin;
    ChainType(JTAG);
AlteraEnd;" > ${filename}".cdf"

    quartus_pgm -c ${cable_index} ${filename}.cdf
    rm ${filename}.cdf
    echo "Done."
fi
