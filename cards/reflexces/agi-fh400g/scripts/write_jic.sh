#!/bin/bash
#
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# configuration
cable_index=1 # use jtagconfig command for check cable index

if [ $# != 1 ] ; then
    echo "Usage:"
    echo "------"
    echo "    sh write_jic.sh <input jic file>"
    echo " "
    echo "Example:"
    echo "    sh write_jic.sh my_firmware.jic"
    exit
fi

file=$1
filename=${file%.*}
extension=${file##*.}

if [ $extension != "jic" ] ; then
    echo "Only .jic file is allowed!"
    exit
fi

if [ $extension == "jic" ] ; then
    touch ${filename}".cdf"
    echo "/* Quartus Prime Version 22.1.0 Build 174 03/30/2022 SC Pro Edition */
JedecChain;
    FileRevision(JESD32A);
    DefaultMfr(6E);

    P ActionCode(Cfg)
        Device PartName(AGIB027R29AR0) File(\"$file\") MfrSpec(OpMask(1) SEC_Device(MT25QU01G) Child_OpMask(1 1));

ChainEnd;

AlteraBegin;
    ChainType(JTAG);
AlteraEnd;" > ${filename}".cdf"

    # Set JTAG frequency
    jtagconfig --setparam ${cable_index} JtagClock 6M
    # Write .jic file to FPGA
    quartus_pgm -c ${cable_index} ${filename}.cdf
    # Clean
    rm ${filename}.cdf
    echo "Done."
fi
