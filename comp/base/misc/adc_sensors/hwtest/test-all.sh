#!/bin/bash
# test-all.sh: Used for reading all the values from the ADC and displaying them to stdout
# Copyright (C) 2019 CESNET
# Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Getting input address
addr_base=$1

######################################
# GENERATING CONF ADDRESSES
######################################
conf_addr=$addr_base
printf -v addr_base '%x' $(($addr_base+0x4))
ctrl_addr=$addr_base
printf -v addr_base '%x' $((16#$addr_base+0x4))
stat_addr=$addr_base

######################################
# GENERATING TEMP ADDRESSES
######################################
for number in {0..8}
do
    if [ $number == 0 ]
    then
        printf -v addr_base '%x' $((16#$addr_base+0x8))
    else
        printf -v addr_base '%x' $((16#$addr_base+0x4))
    fi
    eval "temp${number}_addr"=$addr_base
done

######################################
# GENERATING VOLT ADDRESSES
######################################
for number in {0..15}
do
    if [ $number == 0 ]
    then
        printf -v addr_base '%x' $((16#$addr_base+0x10))
    else
        printf -v addr_base '%x' $((16#$addr_base+0x4))
    fi
    eval "volt${number}_addr"=$addr_base
done


######################################
# SETUP
######################################
nfb-bus $conf_addr 0xFFFF01FF
nfb-bus $ctrl_addr 0x00010001

######################################
# WAIT FOR ADC
######################################
stat=$(nfb-bus $stat_addr)

while [[ "$stat" != "ffff007f" ]]
do
    stat=$(nfb-bus $stat_addr)
done

echo   "+--------------------------------------------+"
echo   "|               Status Registers             |"
echo   "+--------------------------------------------+"
printf "|conf                        |  %12s |\n" $(nfb-bus $conf_addr)
printf "|ctrl                        |  %12s |\n" $(nfb-bus $ctrl_addr)
printf "|stat                        |  %12s |\n" $(nfb-bus $stat_addr)

######################################
# GET ALL THE VALUES
######################################
temp0=$(./valcon -t $(nfb-bus $temp0_addr))
temp1=$(./valcon -t $(nfb-bus $temp1_addr))
temp2=$(./valcon -t $(nfb-bus $temp2_addr))
temp3=$(./valcon -t $(nfb-bus $temp3_addr))
temp4=$(./valcon -t $(nfb-bus $temp4_addr))
temp5=$(./valcon -t $(nfb-bus $temp5_addr))
temp6=$(./valcon -t $(nfb-bus $temp6_addr))
temp7=$(./valcon -t $(nfb-bus $temp7_addr))
temp8=$(./valcon -t $(nfb-bus $temp8_addr))
volt0=$(./valcon -v $(nfb-bus $volt0_addr))
volt1=$(./valcon -v $(nfb-bus $volt1_addr))
volt2=$(./valcon -v $(nfb-bus $volt2_addr))
volt3=$(./valcon -v $(nfb-bus $volt3_addr))
volt4=$(./valcon -v $(nfb-bus $volt4_addr))
volt5=$(./valcon -v $(nfb-bus $volt5_addr))
volt6=$(./valcon -v $(nfb-bus $volt6_addr))
volt7=$(./valcon -v $(nfb-bus $volt7_addr))
volt8=$(./valcon -v $(nfb-bus $volt8_addr))
volt9=$(./valcon -v $(nfb-bus $volt9_addr))
volt10=$(./valcon -v $(nfb-bus $volt10_addr))
volt11=$(./valcon -v $(nfb-bus $volt11_addr))
volt12=$(./valcon -v $(nfb-bus $volt12_addr))
volt13=$(./valcon -v $(nfb-bus $volt13_addr))
volt14=$(./valcon -v $(nfb-bus $volt14_addr))
volt15=$(./valcon -v $(nfb-bus $volt15_addr))

######################################
# OUTPUT
######################################
echo   "+--------------------------------------------+"
echo   "|                Temperatures                |"
echo   "+--------------------------------------------+"
printf "|Channel 0 (Core Fabric)     |  %10s °C|\n" $temp0
printf "|Channel 1 (1C,1D,1E,1F,8A)  |  %10s °C|\n" $temp1
printf "|Channel 2 (1G,1H,1I,1J,8B)  |  %10s °C|\n" $temp2
printf "|Channel 3 (1K,1L,1M,1N,8C)  |  %10s °C|\n" $temp3
printf "|Channel 4 (4C,4D,4E,4F,9A)  |  %10s °C|\n" $temp4
printf "|Channel 5 (4G,4H,4I,4J,9B)  |  %10s °C|\n" $temp5
printf "|Channel 6 (4K,4L,4M,4N,9C)  |  %10s °C|\n" $temp6
printf "|Channel 7 (HBM2)            |  %10s °C|\n" $temp7
printf "|Channel 8 (HBM2)            |  %10s °C|\n" $temp8
echo   "+--------------------------------------------+"
echo   "|                  Voltages                  |"
echo   "+--------------------------------------------+"
printf "|Channel 0  (VSIGP/VISGN)    |  %11s V|\n" $volt0
printf "|Channel 1  (VSIGP/VSIGN)    |  %11s V|\n" $volt1
printf "|Channel 2  (VCC)            |  %11s V|\n" $volt2
printf "|Channel 3  (VCCIO_SDM)      |  %11s V|\n" $volt3
printf "|Channel 4  (VCCPT)          |  %11s V|\n" $volt4
printf "|Channel 5  (Reserved)       |  %11s V|\n" $volt5
printf "|Channel 6  (VCCERAM)        |  %11s V|\n" $volt6
printf "|Channel 7  (Reserved)       |  %11s V|\n" $volt7
printf "|Channel 8  (Reserved)       |  %11s V|\n" $volt8
printf "|Channel 9  (VCCADC)         |  %11s V|\n" $volt9
printf "|Channel 10 (Reserved)       |  %11s V|\n" $volt10
printf "|Channel 11 (Reserved)       |  %11s V|\n" $volt11
printf "|Channel 12 (Reserved)       |  %11s V|\n" $volt12
printf "|Channel 13 (Reserved)       |  %11s V|\n" $volt13
printf "|Channel 14 (Reserved)       |  %11s V|\n" $volt14
printf "|Channel 14 (Reserved)       |  %11s V|\n" $volt15
echo   "+--------------------------------------------+"
printf "|stat                        |  %12s |\n" $(nfb-bus $stat_addr)
echo   "+--------------------------------------------+"
