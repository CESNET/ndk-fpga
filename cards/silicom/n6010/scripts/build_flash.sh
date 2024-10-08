#!/bin/bash
# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

#

FACTORY_SOF="fpga.sof"
FACTORY_HPS_SOF="fpga_hps.sof"
pfg_file="fpga.pfg"
pfg_hps_file="fpga_hps.pfg"
pfg_flash_file="fpga_flash.pfg"
pfg_hps_flash_file="fpga_hps_flash.pfg"
fme_mif_file="fme_id.mif"
factory_image_info_file="factory_image_info.hex"
user1_image_info_file="user1_image_info.hex"
user2_image_info_file="user2_image_info.hex"
factory_image_info_text="factory_image_info.txt"
user1_image_info_text="user1_image_info.txt"
user2_image_info_text="user2_image_info.txt"
pacsign_infile_factory="fpga_page0_factory.bin"
pacsign_infile_user1="fpga_page1_user1.bin"
pacsign_infile_user2="fpga_page2_user2.bin"
pacsign_outfile_factory="fpga_page0_pacsign_factory.bin"
pacsign_outfile_user1="fpga_page1_pacsign_user1.bin"
pacsign_outfile_user2="fpga_page2_pacsign_user2.bin"
FACTORY_SOF_PRESENT="0"
FACTORY_HPS_SOF_PRESENT="0"
GEN_TYPE=""

# This script assumes that the calling shell has already changed the CWD 
# to this directory.
SCRIPT=$(realpath "$0")
WORK_DIR=`realpath .`
LOCAL_SCRIPT_DIR=$(dirname "$SCRIPT")

# check for factory_image.sof, if not available, 
# copy over the ofs_fim.sof as the factory
if [ -e ${WORK_DIR}/${FACTORY_HPS_SOF} ]; then
   echo "Using ${FACTORY_HPS_SOF} as the factory image."
   #cp --remove-destination ${LOCAL_SCRIPT_DIR}/../${FACTORY_HPS_SOF} ${LOCAL_SCRIPT_DIR}/${FACTORY_HPS_SOF}
   FACTORY_HPS_SOF_PRESENT="1"
   GEN_TYPE="fpga_hps"
   echo ""
else
    if [ -e ${WORK_DIR}/${FACTORY_SOF} ]; then
       echo "No ${FACTORY_HPS_SOF} factory image found, but ${FACTORY_SOF} exists."
       echo "Copying over ${FACTORY_SOF} as the factory image."
       #cp --remove-destination ${LOCAL_SCRIPT_DIR}/../${FACTORY_SOF} ${LOCAL_SCRIPT_DIR}/${FACTORY_SOF}
       FACTORY_SOF_PRESENT="1"
       GEN_TYPE="fpga"
       echo ""
    else
        echo "Cannot find ${FACTORY_HPS_SOF} nor ${WORK_DIR}/${FACTORY_SOF}."
        exit 1
    fi
fi

# Creating Image Info Files for Flash Generation
python3 ${LOCAL_SCRIPT_DIR}/gen_image_info_hex.py ${LOCAL_SCRIPT_DIR}/${fme_mif_file} ${WORK_DIR}/${factory_image_info_file} ${WORK_DIR}/${factory_image_info_text}
python3 ${LOCAL_SCRIPT_DIR}/gen_image_info_hex.py ${LOCAL_SCRIPT_DIR}/${fme_mif_file} ${WORK_DIR}/${user1_image_info_file} ${WORK_DIR}/${user1_image_info_text}
python3 ${LOCAL_SCRIPT_DIR}/gen_image_info_hex.py ${LOCAL_SCRIPT_DIR}/${fme_mif_file} ${WORK_DIR}/${user2_image_info_file} ${WORK_DIR}/${user2_image_info_text}

## blank bmc key - 4 bytes of FF
#python reverse.py blank_bmc_key_programmed blank_bmc_key_programmed.reversed
#objcopy -I binary -O ihex ${LOCAL_SCRIPT_DIR}/blank_bmc_key_programmed.reversed ${LOCAL_SCRIPT_DIR}/blank_bmc_key_programmed.reversed.hex

## blank bmc root key hash - 32 bytes of FF
#python ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/blank_bmc_root_hash ${LOCAL_SCRIPT_DIR}/blank_bmc_root_hash.reversed
#objcopy -I binary -O ihex ${LOCAL_SCRIPT_DIR}/blank_bmc_root_hash.reversed ${LOCAL_SCRIPT_DIR}/blank_bmc_root_hash.reversed.hex

## blank sr (FIM) key - 4 bytes of FF
#python ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/blank_sr_key_programmed ${LOCAL_SCRIPT_DIR}/blank_sr_key_programmed.reversed 
#objcopy -I binary -O ihex blank_sr_key_programmed.reversed blank_sr_key_programmed.reversed.hex

## blank sr (FIM) root key hash - 32 bytes of FF
#python ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/blank_sr_root_hash ${LOCAL_SCRIPT_DIR}/blank_sr_root_hash.reversed
#objcopy -I binary -O ihex ${LOCAL_SCRIPT_DIR}/blank_sr_root_hash.reversed ${LOCAL_SCRIPT_DIR}/blank_sr_root_hash.reversed.hex


### option bits
#objcopy -I binary -O ihex ${LOCAL_SCRIPT_DIR}/pac_d5005_option_bits ${LOCAL_SCRIPT_DIR}/pac_d5005_option_bits.hex

### pac_d5005_rot_xip_factory>bin.reversed
#python ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory.bin ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory.bin.reversed
#objcopy -I binary -O ihex pac_d5005_rot_xip_factory.bin.reversed pac_d5005_rot_xip_factory.bin.reversed.hex

### pac_d5005_rot_xip_factory_header.bin.reversed
#python ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory_header.bin ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory_header.bin.reversed
#objcopy -I binary -O ihex ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory_header.bin.reversed ${LOCAL_SCRIPT_DIR}/pac_d5005_rot_xip_factory_header.bin.reversed.hex


# -- generate very special pof with no root entry hash information
# NOTE: This pass will generate the POF used for creating a condensed Flash image.
#       The POF for general use will be created after creating the unsigned Flash BIN below.
echo ">>> Generating POF for Flash BIN Creation (SOF Image Auto Size) <<<"
if [ $FACTORY_HPS_SOF_PRESENT = "1" ]; then
   if [ -e "${LOCAL_SCRIPT_DIR}/${pfg_hps_flash_file}" ]; then
      echo "Using PFG file ${pfg_hps_flash_file}."
      #cd "${LOCAL_SCRIPT_DIR}/.."
      quartus_pfg -c ${LOCAL_SCRIPT_DIR}/$pfg_hps_flash_file
   else
      echo "Cannot find PFG file: ${pfg_hps_flash_file}."
      exit 1
   fi
else
   if [ $FACTORY_SOF_PRESENT = "1" ]; then
      if [ -e "${LOCAL_SCRIPT_DIR}/${pfg_flash_file}" ]; then
         echo "Using PFG file ${pfg_flash_file}."
         #cd "${LOCAL_SCRIPT_DIR}/.."
         quartus_pfg -c ${LOCAL_SCRIPT_DIR}/$pfg_flash_file
      else
         echo "Cannot find PFG file: ${pfg_flash_file}."
         exit 1
      fi
   else
      echo "There are no valid SOFs present to process."
      exit 1
   fi
fi
# ------------------------------------------------------------------------------------------

#if [ -e "${LOCAL_SCRIPT_DIR}/../${pfg_file}" ]; then
#   echo "Using PFG file ${pfg_file}"
#   cd "${LOCAL_SCRIPT_DIR}/.."
#   quartus_pfg -c $pfg_file
#else
#   echo "Cannot find ${pfg_file}"
#   exit 1
#fi


# -- generate ihex from pof
quartus_cpf -c ${WORK_DIR}/${GEN_TYPE}.pof ${WORK_DIR}/${GEN_TYPE}.hexout


# -- convert to ihex to bin
objcopy -I ihex -O binary ${WORK_DIR}/${GEN_TYPE}.hexout ${WORK_DIR}/${GEN_TYPE}.bin


python3 ${LOCAL_SCRIPT_DIR}/extract_bitstream.py ${WORK_DIR}/${GEN_TYPE}_pof.map ${WORK_DIR}/${GEN_TYPE}.bin ${WORK_DIR}/$pacsign_infile_factory "Factory_Image"
python3 ${LOCAL_SCRIPT_DIR}/extract_bitstream.py ${WORK_DIR}/${GEN_TYPE}_pof.map ${WORK_DIR}/${GEN_TYPE}.bin ${WORK_DIR}/$pacsign_infile_user1 "User_Image_1"
python3 ${LOCAL_SCRIPT_DIR}/extract_bitstream.py ${WORK_DIR}/${GEN_TYPE}_pof.map ${WORK_DIR}/${GEN_TYPE}.bin ${WORK_DIR}/$pacsign_infile_user2 "User_Image_2"

# -- read the image info txt string to pass to pacsign 
value_factory=$(<${LOCAL_SCRIPT_DIR}/../${factory_image_info_text})
value_user1=$(<${LOCAL_SCRIPT_DIR}/../${user1_image_info_text})
value_user2=$(<${LOCAL_SCRIPT_DIR}/../${user2_image_info_text})


# -- generate manufacturing image for 3rd party programmer to write to flash before board assembly
# uncomment following line if mfg image is desired
#python3 ${LOCAL_SCRIPT_DIR}/reverse.py ${LOCAL_SCRIPT_DIR}/../${GEN_TYPE}.bin ${LOCAL_SCRIPT_DIR}/../mfg_ofs_fim_reversed.bin

# -- create unsigned FIM user image for fpgasupdate tool 
if which PACSign &> /dev/null ; then
    PACSign FACTORY -y -v -t UPDATE -H openssl_manager  -b ${value_factory} -i ${WORK_DIR}/$pacsign_infile_factory -o ${WORK_DIR}/$pacsign_outfile_factory
    PACSign SR -s 0 -y -v -t UPDATE -H openssl_manager  -b ${value_factory} -i ${WORK_DIR}/$pacsign_infile_user1 -o ${WORK_DIR}/$pacsign_outfile_user1
    PACSign SR -s 1 -y -v -t UPDATE -H openssl_manager  -b ${value_factory} -i ${WORK_DIR}/$pacsign_infile_user2 -o ${WORK_DIR}/$pacsign_outfile_user2
else
    echo "PACSign not found! Please manually sign ../$pacsign_infile." 1>&2
fi

# -- NOW: generate POF with maximum file sizes for general use.
echo ">>> Generating POF for General Purpose Use (SOF Image Maximum Size) <<<"
if [ $FACTORY_HPS_SOF_PRESENT = "1" ]; then
   if [ -e "${LOCAL_SCRIPT_DIR}/${pfg_hps_file}" ]; then
      echo "Using PFG file ${pfg_hps_file}."
      #cd "${LOCAL_SCRIPT_DIR}/.."
      quartus_pfg -c ${LOCAL_SCRIPT_DIR}/$pfg_hps_file
   else
      echo "Cannot find PFG file: ${pfg_hps_file}."
      exit 1
   fi
else
   if [ $FACTORY_SOF_PRESENT = "1" ]; then
      if [ -e "${LOCAL_SCRIPT_DIR}/${pfg_file}" ]; then
         echo "Using PFG file ${pfg_file}."
         #cd "${LOCAL_SCRIPT_DIR}/.."
         quartus_pfg -c ${LOCAL_SCRIPT_DIR}/$pfg_file
      else
         echo "Cannot find PFG file: ${pfg_file}."
         exit 1
      fi
   else
      echo "There are no valid SOFs present to process."
      exit 1
   fi
fi

echo "Done."
exit 0