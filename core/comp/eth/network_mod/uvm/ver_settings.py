# ver_settings.py
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

SETTINGS = {
    "default" : {
        "ETH_CORE_ARCH"                  :  "\\\"E_TILE\\\"",
        "ETH_PORTS"                      :  "2",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{100}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "4",
        "REGIONS"                        : "1",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"STRATIX10\\\"",
        "BOARD"                          : "\\\"DUMMY\\\"",
        "PACKET_SIZE_MIN"                : "64",
        "PACKET_SIZE_MAX"                : "1500",
        "__core_params__": {
            "UVM_TEST": "test::base",
            "NETWORK_ARCH": "E_TILE"
        },
    },

    "etile_1x100g4" : {
        "ETH_CORE_ARCH"                  :  "\\\"E_TILE\\\"",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{100}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "4",
        "REGIONS"                        : "1",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"AGILEX\\\"",
        "__core_params__": {
            "UVM_TEST": "test::base",
            "NETWORK_ARCH": "E_TILE"
        },
    },

    "etile_4x10g1" : {
        "ETH_CORE_ARCH"                  :  "\\\"E_TILE\\\"",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{10}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "4",
        "REGIONS"                        : "1",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"AGILEX\\\"",
        "__core_params__": {
            "UVM_TEST": "test::base",
            "NETWORK_ARCH": "E_TILE"
        },
    },

    "ftile_1x400g8" : {
        "ETH_CORE_ARCH"                  :  "\\\"F_TILE\\\"",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{400}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "8",
        "REGIONS"                        : "4",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"AGILEX\\\"",
        "__core_params__": {
            "UVM_TEST": "test::base",
            "NETWORK_ARCH": "F_TILE"
        },
    },

    "ftile_1x100g4" : {
        "ETH_CORE_ARCH"                  :  "\\\"F_TILE\\\"",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{100}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "8",
        "REGIONS"                        : "4",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"AGILEX\\\"",
        "__core_params__": {
            "UVM_TEST": "test::base",
            "NETWORK_ARCH": "F_TILE"
        },
    },

    "cmac_1x100g4" : {
        "ETH_CORE_ARCH"                  :  "\\\"CMAC\\\"",
        "int unsigned ETH_PORT_SPEED\\[ETH_PORTS-1:0\\]"  : "'{ETH_PORTS{100}}",
        "int unsigned ETH_PORT_CHAN\\[ETH_PORTS-1:0\\]" : "'{ETH_PORTS{1}}",
        "LANES"                          : "4",
        "REGIONS"                        : "1",
        "REGION_SIZE"                    : "8",
        "BLOCK_SIZE"                     : "8",
        "ITEM_WIDTH"                     : "8",
        "DEVICE"                         : "\\\"ULTRASCALE\\\"",
        "__core_params__": {"NETWORK_ARCH": "CMAC"},

    },

    "ports_1" : {
        "ETH_PORTS"                      :  "1",
    },

    "ports_2" : {
        "ETH_PORTS"                      :  "2",
    },

    "ports_4" : {
        "ETH_PORTS"                      :  "4",
    },

    "etile_test_speed" : {
        "__core_params__": {
            "UVM_TEST": "test::speed",
            "NETWORK_ARCH": "E_TILE"
        },
    },

    "ftile_test_speed" : {
        "__core_params__": {
            "UVM_TEST": "test::speed",
            "NETWORK_ARCH": "F_TILE"
        },
    },

    "large_packets" : {
        "PACKET_SIZE_MIN"                : "12000",
        "PACKET_SIZE_MAX"                : "16384",
    },

    "small_packets" : {
        "PACKET_SIZE_MIN"                : "64",
        "PACKET_SIZE_MAX"                : "128",
    },

    "_combinations_" : {
        # 2x E-Tile 100G
        "2p_etile_1x100g4_normal"       : ("etile_1x100g4", "ports_2",),
        "2p_etile_1x100g4_small"        : ("etile_1x100g4", "ports_2", "small_packets",),
        "2p_etile_1x100g4_large"        : ("etile_1x100g4", "ports_2", "large_packets",),
        "2p_etile_1x100g4_normal_speed" : ("etile_1x100g4", "ports_2", "small_packets", "etile_test_speed",),
        "2p_etile_1x100g4_small_speed"  : ("etile_1x100g4", "ports_2", "large_packets", "etile_test_speed",),

        # TODO UNSUPPORTED: ONLY ONE CHANNEL PER PORT
        # 2x E-Tile 4x10G
        #"2p_etile_4x10g1_normal"        : ("etile_4x10g1", "ports_2",),
        #"2p_etile_4x10g1_small"         : ("etile_4x10g1", "ports_2", "small_packets",),
        #"2p_etile_4x10g1_large"         : ("etile_4x10g1", "ports_2", "large_packets",),
        #"2p_etile_4x10g1_normal_speed"  : ("etile_4x10g1", "ports_2", "small_packets", "etile_test_speed",),
        #"2p_etile_4x10g1_small_speed"   : ("etile_4x10g1", "ports_2", "large_packets", "etile_test_speed",),

        # 1x F-Tile 400G
        "1p_ftile_1x400g8_normal"       : ("ftile_1x400g8", "ports_1",),
        "1p_ftile_1x400g8_small"        : ("ftile_1x400g8", "ports_1", "small_packets",),
        "1p_ftile_1x400g8_large"        : ("ftile_1x400g8", "ports_1", "large_packets",),
        "1p_ftile_1x400g8_normal_speed" : ("ftile_1x400g8", "ports_1", "small_packets", "ftile_test_speed",),
        "1p_ftile_1x400g8_small_speed"  : ("ftile_1x400g8", "ports_1", "large_packets", "ftile_test_speed",),

        # 1x F-Tile 2x100G
        "1p_ftile_1x100g4_normal"       : ("ftile_1x100g4", "ports_1",),
        "1p_ftile_1x100g4_small"        : ("ftile_1x100g4", "ports_1", "small_packets",),
        "1p_ftile_1x100g4_large"        : ("ftile_1x100g4", "ports_1", "large_packets",),
        "1p_ftile_1x100g4_normal_speed" : ("ftile_1x100g4", "ports_1", "small_packets", "ftile_test_speed",),
        "1p_ftile_1x100g4_small_speed"  : ("ftile_1x100g4", "ports_1", "large_packets", "ftile_test_speed",),

        # TODO UNSUPPORTED: CMAC IS NOT IMPLEMENTED
        # 2x CMAC 100G
        #"2p_cmac_1x100g4_normal"       : ("cmac_1x100g4", "ports_2",),
        #"2p_cmac_1x100g4_small"        : ("cmac_1x100g4", "ports_2", "small_packets",),
        #"2p_cmac_1x100g4_large"        : ("cmac_1x100g4", "ports_2", "large_packets",),
        #"2p_cmac_1x100g4_normal_speed" : ("cmac_1x100g4", "ports_2", "small_packets", "test_speed",),
        #"2p_cmac_1x100g4_small_speed"  : ("cmac_1x100g4", "ports_2", "large_packets", "test_speed",),

        # 4x CMAC 100G
        #"4p_cmac_1x100g4_normal"       : ("cmac_1x100g4", "ports_4",),
        #"4p_cmac_1x100g4_small"        : ("cmac_1x100g4", "ports_4", "small_packets",),
    },
}