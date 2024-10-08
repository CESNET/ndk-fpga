#!/bin/bash
#
# Min-max voltage checking script for Virtex-7 XADC
# Viktor Pus <pus@cesnet.cz>
#
# License
#
# Copyright (C) 2014 CESNET
#
# SPDX-License-Identifier: BSD-3-Clause

function hex2volt {
   hexval=`echo $1 | cut -c5-7`
   decval=`echo $((0x${hexval}))`
   voltage=$(echo "scale=4; $decval/4096*3" | bc)
   echo $voltage
}

function read_stats {
   # set sequencer
   csbus 44 2
   csbus A0 7700

   # Read actual values
   csbus 44 0

   vccint=$(hex2volt `csbus 84`)
   vccaux=$(hex2volt `csbus 88`)
   vccbram=$(hex2volt `csbus 98`)

   # Read min-max values
   csbus 44 1

   vccint_max=$(hex2volt `csbus 84`)
   vccaux_max=$(hex2volt `csbus 88`)
   vccbram_max=$(hex2volt `csbus 8c`)
   vccint_min=$(hex2volt `csbus 94`)
   vccaux_min=$(hex2volt `csbus 98`)
   vccbram_min=$(hex2volt `csbus 9c`)

   echo "vccint_min  = $vccint_min"
   echo "vccint      = $vccint"
   echo "vccint_max  = $vccint_max"
   echo "==="
   echo "vccaux_min  = $vccaux_min"
   echo "vccaux      = $vccaux"
   echo "vccaux_max  = $vccaux_max"
   echo "==="
   echo "vccbram_min = $vccbram_min"
   echo "vccbram     = $vccbram"
   echo "vccbram_max = $vccbram_max"
}

function reset {
   csbus 44 0
   csbus 8C 0
}

function usage {
   echo "Usage:"
   echo "-r (reset XADC)"
   echo "-s (read XADC status)"
   echo "-h (print this help)"
}

while getopts "rhs" opt; do
   case $opt in
      h)
         usage
         exit
         ;;
      r)
         echo "Resetting XADC ..."
         reset
         exit
         ;;
      s)
         echo "Reading XADC status ..."
         read_stats
         exit
         ;;
      \?)
         usage
         exit
         ;;
   esac
done

usage
