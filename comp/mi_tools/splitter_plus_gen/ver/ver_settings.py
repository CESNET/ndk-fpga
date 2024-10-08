# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ADDR_WIDTH"                                           : "8",
        "DATA_WIDTH"                                           : "8",
        "META_WIDTH"                                           : "8",
        "PORTS"                                                : "8",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{0,1,1,0,1,0,0,0}",
        "ADDR_MASK"                                            : "8'b11110000",
        "ADDR_BASES"                                           : "8",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000,8'b00011000,8'b00100000,8'b01000000,8'b01100000,8'b10000000,8'b10100000,8'b11000000}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{1,0,0,2,0,0,0,3}",
        "TRANSACTION_COUNT"                                    : "10000",
    },
    "number_of_ports_comb_1" : {
        "PORTS"                                                : "10",
        "ADDR_BASES"                                           : "10",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000,8'b00011000,8'b00100000,8'b01000000,8'b01100000,8'b10000000,8'b10100000,8'b11000000,8'b11010000,8'b11100000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{0,1,1,0,1,0,0,0,1,0}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{0,1,2,3,4,5,6,7,0,0}",
    },
    "number_of_ports_comb_2" : {
        "PORTS"                                                : "2",
        "ADDR_BASES"                                           : "2",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000,8'b00011000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{0,1}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{1,0}",
    },
    "number_of_ports_comb_3" : {
        "PORTS"                                                : "1",
        "ADDR_BASES"                                           : "1",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{1}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{0}",
    },
    "number_of_ports_comb_4" : {
        "PORTS"                                                : "1",
        "ADDR_BASES"                                           : "1",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{0}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{0}",
    },
    "number_of_ports_comb_5" : {
        "PORTS"                                                : "10",
        "ADDR_BASES"                                           : "10",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000,8'b00011000,8'b00100000,8'b01000000,8'b01100000,8'b10000000,8'b10100000,8'b11000000,8'b11010000,8'b11100000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{1,1,1,1,1,1,1,1,1,1}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{0,1,2,3,4,5,6,7,8,9}",
    },
    "number_of_ports_comb_6" : {
        "PORTS"                                                : "10",
        "ADDR_BASES"                                           : "10",
        "logic \\[ADDR_WIDTH-1:0\\] ADDR_BASE\\[ADDR_BASES\\]" : "{8'b00000000,8'b00011000,8'b00100000,8'b01000000,8'b01100000,8'b10000000,8'b10100000,8'b11000000,8'b11010000,8'b11100000}",
        "logic PIPE_OUT\\[PORTS-1:0\\]"                         : "{0,1,0,0,0,0,0,0,0,0}",
        "int PORT_MAPPING\\[ADDR_BASES\\]"                     : "{0,1,0,0,0,0,0,0,0,0}",
    },
    "meta_comb_1" : {
        "META_WIDTH"                                           : "16",
    },
    "meta_comb_2" : {
        "META_WIDTH"                                           : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("number_of_ports_comb_1",),
    ("number_of_ports_comb_2",),
    ("number_of_ports_comb_3",),
    ("number_of_ports_comb_4",),
    ("number_of_ports_comb_5",),
    ("number_of_ports_comb_6",),

    ("number_of_ports_comb_1","meta_comb_1",),
    ("number_of_ports_comb_2","meta_comb_1",),
    ("number_of_ports_comb_3","meta_comb_1",),
    ("number_of_ports_comb_4","meta_comb_1",),
    ("number_of_ports_comb_5","meta_comb_1",),
    ("number_of_ports_comb_6","meta_comb_1",),

    ("number_of_ports_comb_1","meta_comb_2",),
    ("number_of_ports_comb_2","meta_comb_2",),
    ("number_of_ports_comb_3","meta_comb_2",),
    ("number_of_ports_comb_4","meta_comb_2",),
    ("number_of_ports_comb_5","meta_comb_2",),
    ("number_of_ports_comb_6","meta_comb_2",),
    ),
}
