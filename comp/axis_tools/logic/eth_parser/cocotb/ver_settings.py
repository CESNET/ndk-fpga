# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default": {
        "DUT_ENTITY":      "AXIS_ETH_PARSER_GEN",
        "AXI_TDATA_WIDTH": "512",
        "PROTOCOLS_STR":   "eth-vlan-vlan-mpls-mpls-ipv4-ipv6-ipv6ext-ipv6ext-tcp-udp",
        "PKT_MTU":         "16384",
        "FIFO_DEPTH":      "64",
        "STAGE_REG_AUTO":  "True",
        "STAGE_REG_MASK":  "0",
    },

    "bus_128": {
        "AXI_TDATA_WIDTH": "128",
    },

    "bus_256": {
        "AXI_TDATA_WIDTH": "256",
    },

    "bus_1024": {
        "AXI_TDATA_WIDTH": "1024",
    },

    "mtu_2k": {
        "PKT_MTU": "2048",
    },

    "mtu_1k": {
        "PKT_MTU": "1024",
    },

    "small_fifo": {
        "FIFO_DEPTH": "16",
    },

    # Protocol set of AXIS_ETH_PARSER
    "proto_basic": {
        "PROTOCOLS_STR": "eth-vlan-ipv4-tcp-udp",
    },

    "wrapper": {
        "DUT_ENTITY":    "AXIS_ETH_PARSER",
        "PROTOCOLS_STR": "eth-vlan-ipv4-tcp-udp",
    },

    # Three stages of VLAN, MPLS and IPV6EXT, without IPv4 and TCP
    "proto_deep": {
        "PROTOCOLS_STR": "eth-vlan-vlan-vlan-mpls-mpls-mpls-ipv6-ipv6ext-ipv6ext-ipv6ext-udp",
    },

    # Register stage after every stage
    "reg_all": {
        "STAGE_REG_AUTO": "False",
        "STAGE_REG_MASK": "2147483647",
    },

    "reg_none": {
        "STAGE_REG_AUTO": "False",
        "STAGE_REG_MASK": "0",
    },

    # Register stages after stages 0, 2, 5 and 6
    "reg_pattern": {
        "STAGE_REG_AUTO": "False",
        "STAGE_REG_MASK": "101",
    },

    "_combinations_": (
        (),
        ("bus_128",),
        ("bus_256", "mtu_2k"),
        ("bus_1024",),
        ("small_fifo",),
        ("mtu_1k",),
        ("proto_basic",),
        ("proto_basic", "bus_256"),
        ("wrapper",),
        ("wrapper", "bus_128"),
        ("wrapper", "bus_256", "mtu_2k"),
        ("wrapper", "bus_1024"),
        ("proto_deep",),
        ("proto_deep", "bus_128", "mtu_1k"),
        ("proto_deep", "bus_256"),
        ("reg_all",),
        ("reg_all", "bus_128", "small_fifo"),
        ("reg_none", "bus_256"),
        ("reg_pattern", "bus_1024"),
        ("reg_pattern", "proto_deep", "bus_256"),
    ),
}
