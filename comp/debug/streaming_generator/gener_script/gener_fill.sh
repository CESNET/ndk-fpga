# \file:   gener_fill.vhd
# \brief:
# \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
# \date 2014
#
# \section License
#
# Copyright (C) 2014 CESNET
#
# SPDX-License-Identifier: BSD-3-Clause
#

#!/bin/bash


HELP="
# Usage: ./gener_fill.sh [-hiv] [-fnad dec] [-b hex] [-m (0,1,2)] [-p (dec<65536, x%)] [-e (0,1)] [-l file]
# -h     : help
# -b     : set Base address
# -i     : print info (version, RANDOM, CNT_WIDTH, ITEMS, DATA_WIDTH, DST_RDY ...)
# -f     : set number of generated values (0 => infinity)
# -n     : set number of valid values in memory (0 => whole memory)
# -a     : set number of cycles active SRC_RDY
# -d     : set number of cycles deactive SRC_RDY
# -m     : mode generate SRC_RDY (0 => still true, 1 => act,dec cycles, 2 => random)
# -p     : probability of setting SRC_RDY to '1' when mode => 2 (0 => 0%, 65535 => 100%)
# -e     : enbale/run/start generating data (0 => stop, 1 => start)
# -l     : load the data into memory from file
# -v     : print information when data is being recorded to the memory (-l [file])
"

base_addr=0
conv_variable=0

function conv () {
   if [[ ${1:0:2} = "0x" || ${1:0:2} = "0X" ]]; then
      conv_variable=$(($1))
   else
      conv_variable=$((0x$1))
   fi
}

function h_func {
   echo "$HELP"
   exit
}

function b_func {
   conv $OPTARG_b
   base_addr=$(($conv_variable))
}

function i_func {
   local setting1=$(csbus $(printf '%x' $base_addr ))
   local setting2=$(csbus $(printf '%x' $(($base_addr + 0x4))))
   local config1=$(csbus $(printf '%x' $(($base_addr + 0x8))))
   local config2=$(csbus $(printf '%x' $(($base_addr + 0xC))))
   local config3=$(csbus $(printf '%x' $(($base_addr + 0x10))))
   local config4=$(csbus $(printf '%x' $(($base_addr + 0x14))))
   local cmd=$(csbus $(printf '%x' $(($base_addr + 0x18))))

   printf  "   BASE ADDRESS:         "'%#.8X\n' $base_addr
   echo ">SETINGS1"
   printf  "   VERSION:              "'%s\n' "$((0x${setting1:7:8}))"
   printf  "   RANDOM:               true\n"
   printf  "   CNT_WIDTH:            "'%s\n' "$((0x${setting1:0:4}))"
   echo ">SETTINGS2"
   printf  "   ITMES:                "'%s\n' "$((0x${setting2:4:8}))"
   printf  "   DATA_WIDTH:           "'%s\n' "$((0x${setting2:0:4}))"
   echo ">CONFIG1"
   printf  "   VALID_NUM_ITEMS:      "'%s\n' "$((0x${config1:4:8}))"
   printf  "   NUM_OF_GEN_VALUE:     "'%s\n' "$((0x${config1:0:4}))"
   echo ">CONFIG2"
   printf  "   NUM_OF_ACTIVE_SRC:    "'%s\n' "$((0x$config2))"
   echo ">CONFIG3"
   printf  "   NUM_OF_DEACTIVE_SRC:  "'%s\n' "$((0x$config3))"
   echo ">CONFIG4"
   printf  "   GENERATE_MODE:        "'%s\n' "$((0x${config4:7:8}))"
   printf  "   PROBABILITY:          %s - %s%%\n" "$((0x${config4:0:4}))" "$(echo "(($((0x${config4:0:4}))+1) / 655.35 )" | bc)"
   echo ">COMMANDS"
   local pom="$(echo "ibase=16;obase=2;$((0x${cmd:7:8}))" | bc | rev)"
   printf  "   RUN:                  "'%s\n' "${pom:0:1}"
   printf  "   DST_RDY:              "'%s\n' "${pom:1:2}"
}

function f_func {
   local conf1=$(csbus $(printf '%x' $(($base_addr + 0x8))))
   conv_variable=$(printf '%.4x' $OPTARG_f)
   csbus $(printf '%x' $(($base_addr + 0x8))) "${conv_variable:0:4}${conf1:4:8}"
}

function n_func {
   local conf1=$(csbus $(printf '%.8x' $(($base_addr + 0x8))))
   conv_variable=$(printf '%.4x' $OPTARG_v)
   csbus $(printf '%x' $(($base_addr + 0x8))) "${conf1:0:4}${conv_variable:0:4}"
}

function a_func {
   conv_variable=$(printf '%x' $OPTARG_a)
   csbus $(printf '%x' $(($base_addr + 0xC))) $conv_variable
}

function d_func {
   conv_variable=$(printf '%x' $OPTARG_d)
   csbus $(printf '%x' $(($base_addr + 0x10))) $conv_variable
}

function m_func {
   local conf4=$(csbus $(printf '%x' $(($base_addr + 0x14))))
   csbus $(printf '%x' $(($base_addr + 0x14))) "${conf4:0:7}${OPTARG_m:0:1}"
}

function p_func {
   local conf4=$(csbus $(printf '%x' $(($base_addr + 0x14))))
   local out=0
   if [[ ( "$OPTARG_p" = *"%"* ) ]] || (( $OPTARG_p <= 65535 )); then
      if [[ ("$OPTARG_p" = *"%"*) ]]; then
         out=$(echo "(655.35 * ${OPTARG_p//%})/1" | bc)
      else
         out=$(($OPTARG_p))
      fi
      out=$(printf '%.4x' $out)
      csbus $(printf '%x' $(($base_addr + 0x14))) "${out:0:4}${conf4:4:8}"
   else
      echo "ERROR: invalid parameter -p"
   fi
}

function e_func {
   if [[ ( "$OPTARG_e" = *"1"* ) ]]; then
      csbus $(printf '%x' $(($base_addr + 0x18))) "1"
   else
      csbus $(printf '%x' $(($base_addr + 0x18))) "0"
   fi
}

function l_func {
   FILE=$OPTARG_l
   local set2=$(csbus $(printf '%x' $(($base_addr + 0x4))))
   local data_width=$((0x${set2:0:4}))
   local items=$((0x${set2:4:8}))

   #local data_width_log2=$(echo "l( ($((0x${set2:0:4}))+31)/32 )/l(2)" | bc -l)
   #data_width_log2=$(echo "(${data_width_log2:0:11} + 0.999999999999)/1" | bc)
   local items_log2=$(echo "l( $((0x${set2:4:8}))+16 )/l(2)" | bc -l)
   items_log2=$(echo "(${items_log2:0:11}+0.999999999999)/1" | bc)
   local num=0

   while read line; do
      line=${line//\t}
      line=${line// }
      line=${line//-}
      line=${line//_}
      line=${line//.}
      line=${line%%#*}

      if [ -z "$line" ] || (( $num >= 4*$items ));
      then
         continue
      else
         line=$(echo $line | rev)
         echo "1 $num"
         local addr_item=$(($base_addr + 0x40 + $num))
         echo "2 $addr_item"

         for i in `eval echo {0..$(echo "($data_width+31)/32 - 1" | bc)}`
         do
            local word=0
            if ! [ -z "$line" ]; then
               word=$(echo ${line:0:8} | rev)
            fi
            line=$(echo ${line:8})

            addr_word=$(( ($i * 2**$(($items_log2 + 2))) + $addr_item))
            addr_word=$(printf '%.8x' $addr_word)
            csbus  $addr_word $word
            if [ ${array_parm[v]} ]; then
               echo " W csbus  $addr_word $word (item $(( ($num/4) + 1 )), word $(( $i + 1 )))"
               echo " R csbus  $addr_word (out: $(csbus  $addr_word))"
            fi
         done
         num=$(( $num + 4 ))
      fi
   done < $FILE
}

declare -A array_parm

while getopts :vhb:il:n:a:d:m:p:e:f: param
do      case "$param" in

        b) array_parm[b]=true
           OPTARG_b="$OPTARG" ;;
        h) array_parm[h]=true ;;
        d) array_parm[d]=true
           OPTARG_d="$OPTARG" ;;
        f) array_parm[f]=true
           OPTARG_f="$OPTARG" ;;
        n) array_parm[n]=true
           OPTARG_v="$OPTARG" ;;
        a) array_parm[a]=true
           OPTARG_a="$OPTARG" ;;
        m) array_parm[m]=true
           OPTARG_m="$OPTARG" ;;
        p) array_parm[p]=true
           OPTARG_p="$OPTARG" ;;
        e) array_parm[e]=true
           OPTARG_e="$OPTARG" ;;
        l) array_parm[l]=true
           OPTARG_l="$OPTARG" ;;
        v) array_parm[v]=true ;;
        i) array_parm[i]=true ;;
        *) echo "ERROR: invalid parameter." >&2
           exit 1 ;;
        esac
done

for y in `eval echo {b,h,d,f,n,a,m,p,l,i,e}`
         do
            if  [ ${array_parm[$y]} ]; then
               ${y}_func
            fi
         done

