#!/usr/bin/env python3
# Copyright (C) 2020 Intel Corporation.
# SPDX-License-Identifier: MIT

#

import argparse
import logging
import re
import sys
import binascii

logging.basicConfig(level=0)
LOGGER= logging.getLogger(__name__)

def checksum_calc(address, value):
    int_value = int(value, 16)
    int_addr = address
    checksum_val = 0
    addend = 0x08 # Calculate checksum on data width.  This is the width of the data field chosen for the Intel HEX file, 8 bytes.
    checksum_val += addend
    for i in range(0, 2): # Calculate checksum on the address value, passed as integer.
        addend = int_addr & 0xFF
        checksum_val += addend
        int_addr = int_addr >> 8
    for i in range(0, 16): # Calculate checksum on the data value, passed as string of digits (converted at top to hexadecimal integer).
        addend = int_value & 0xFF
        checksum_val += addend
        int_value = int_value >> 8
    checksum_val = -checksum_val & 0xFF
    checksum_return = format(checksum_val, '02X')
    return checksum_return

def bit_reversal(value):
    reversed_value = ""
    for i in range(0,len(value),2): # Grab two hex digits (byte) and reverse the bits.
        byte = value[i:i+2]
        byte_int = int(byte,16)
        byte_reversed = '{:08b}'.format(byte_int)[::-1]
        byte_hex = int(byte_reversed,2)
        byte_reversed_str = format(byte_hex, '02X')
        reversed_value = reversed_value + byte_reversed_str
    return reversed_value

def main(args):
    address = 0x0000
    mif_data = args.mif_file.read().decode('utf-8')
    img_status = "0000000000000000"
    id_location_first  = r'\s+02\s+:\s+([0-9a-fA-F]{16})'
    id_location_second = r'\s+03\s+:\s+([0-9a-fA-F]{16})'

    m = re.search(id_location_first, mif_data)
    if not m:
        LOGGER.error("FIM ID at location 02 not found in MIF data file.")
        sys.exit(1)

    id_first = m.group(1)
    words = id_first
    id_first_bytes = id_first.encode()
    id_first_hex_bytes = binascii.hexlify(id_first_bytes)
    id_first_hex = bit_reversal(str(id_first_hex_bytes, 'utf-8'))
    id_first_hex_front_half = id_first_hex[:16]
    id_first_hex_back_half  = id_first_hex[16:]
    id_first_hex_front_half_checksum = checksum_calc(address, id_first_hex_front_half)
    line_first_front = ":08" + format(address, '04X') + "00" + id_first_hex_front_half.upper() + id_first_hex_front_half_checksum
    lines = line_first_front + "\n"
    address += 8
    id_first_hex_back_half_checksum = checksum_calc(address, id_first_hex_back_half)
    line_first_back = ":08" + format(address, '04X') + "00" + id_first_hex_back_half.upper() + id_first_hex_back_half_checksum
    lines = lines + line_first_back + "\n"
    address += 8

    m = re.search(id_location_second, mif_data)
    if not m:
        LOGGER.error("FIM ID at location 03 not found in MIF data file.")
        sys.exit(1)

    id_second = m.group(1)
    words = words + id_second
    id_second_bytes = id_second.encode()
    id_second_hex_bytes = binascii.hexlify(id_second_bytes)
    id_second_hex = bit_reversal(str(id_second_hex_bytes, 'utf-8')) 
    id_second_hex_front_half = id_second_hex[:16]
    id_second_hex_back_half  = id_second_hex[16:]
    id_second_hex_front_half_checksum = checksum_calc(address, id_second_hex_front_half)
    line_second_front = ":08" + format(address, '04X') + "00" + id_second_hex_front_half.upper() + id_second_hex_front_half_checksum
    lines = lines + line_second_front + "\n"
    address += 8
    id_second_hex_back_half_checksum = checksum_calc(address, id_second_hex_back_half)
    line_second_back = ":08" + format(address, '04X') + "00" + id_second_hex_back_half.upper() + id_second_hex_back_half_checksum
    lines = lines + line_second_back + "\n"
    address += 8

    data_line = img_status
    img_status_first_checksum = checksum_calc(address, data_line)
    line_third = ":08" + format(address, '04X') + "00" + data_line.upper() + img_status_first_checksum
    lines = lines + line_third + "\n"

    line_fourth = ":00000001FF"
    lines = lines + line_fourth + "\n"

    args.out_file.write(lines)
    args.out_text.write(words)


if __name__ == '__main__':

    parser = argparse.ArgumentParser()

    parser.add_argument('mif_file', type=argparse.FileType('rb'),
                        help='MIF file containing FIM ID')
    parser.add_argument('out_file', type=argparse.FileType('w'),
                        help='HEX configuration file output')
    parser.add_argument('out_text', type=argparse.FileType('w'),
                        help='HEX configuration text output')

    args = parser.parse_args()
    main(args)
