# hdr_info.py: Definitions of Frame Headers Constants
# Copyright (C) 2025 CESNET z. s. p. o.
# Author: Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# TODO: this file is provisional
#   read constants in switch.py directly from some configuration file
#   also generate 'config_pack.vhd' based on that configuration file

from scapy.all import Ether, Dot1Q, Dot1AD

HDR_ETH = {
    'class' : Ether,
    'name'  : Ether._name,
    'width' : 14,
    'fields': {
        ( 47,  0): 'dst',
        ( 95, 48): 'src',
        (111, 96): 'type',
    }
}

HDR_VLAN_1Q = {
    'class'  : Dot1Q,
    'name'   : Dot1Q._name,
    'width'  : 4,
    'fields' : {
        (15,  0): 'type',
        (18, 16): 'prio',
        (19, 19): 'dei',
        (31, 20): 'vlan',
    }
}

HDR_VLAN_1AD = {
    'class'  : Dot1AD,
    'name'   : Dot1AD._name,
    'width'  : 4,
    'fields' : {
        (15,  0): 'type',
        (18, 16): 'prio',
        (19, 19): 'dei',
        (31, 20): 'vlan',
    }
}

HDR_DB = {
    0: HDR_ETH,
    1: HDR_VLAN_1Q,
    2: HDR_VLAN_1AD,
}

def get_protocol_class(protocol:int) -> object|None:
    return HDR_DB[protocol]['class'] if protocol in HDR_DB else None

def field_is_supported(protocol:int, range_high:int, range_low:int) -> bool:
    return protocol in HDR_DB and (range_high, range_low) in HDR_DB[protocol]['fields']

def get_field_id(protocol:int, range_high:int, range_low:int) -> str:
    if field_is_supported(protocol, range_high, range_low):
        return HDR_DB[protocol]['fields'][(range_high, range_low)]
    return ''

def get_field_info_str(protocol:int, range_high:int, range_low:int) -> str:
    if field_is_supported(protocol, range_high, range_low):
        return HDR_DB[protocol]['name'] + ' - ' + get_field_id(protocol, range_high, range_low)
    return ''
