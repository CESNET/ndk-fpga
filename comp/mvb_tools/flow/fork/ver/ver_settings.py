# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "OUTPUT_PORTS"      : "2",
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
        "USE_DST_RDY"       : "1",
        "VERSION"           : "\\\"logic\\\"",
        "TRANSACTION_COUNT" : "2000",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "ITEMS"             : "8",
    },
    "items_comb_2" : {
        "ITEMS"             : "1",
    },
    "version_register" : {
        "VERSION"           : "\\\"register\\\"",
    },
    "version_simple" : {
        "VERSION"           : "\\\"simple\\\"",
    },
    "use_dst_rdy_0" : {
        "USE_DST_RDY"       : "0",
    },
    "16_output_ports" : {
        "OUTPUT_PORTS"      : "16",
    },
    "1_output_port" : {
        "OUTPUT_PORTS"      : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("bus_comb_2","version_simple","use_dst_rdy_0",),
    ("bus_comb_2","version_register","use_dst_rdy_0",),
    ("bus_comb_2","use_dst_rdy_0",),

    ("version_register",),
    ("version_register","16_output_ports",),
    ("version_register","1_output_port",),
    ("version_simple",),
    ("version_simple","16_output_ports",),
    ("version_simple","1_output_port",),
    ("16_output_ports",),
    ("1_output_port",),

    ("items_comb_1","version_register",),
    ("items_comb_1","version_register","16_output_ports",),
    ("items_comb_1","version_register","1_output_port",),
    ("items_comb_1","version_simple",),
    ("items_comb_1","version_simple","16_output_ports",),
    ("items_comb_1","version_simple","1_output_port",),
    ("items_comb_1","16_output_ports",),
    ("items_comb_1","1_output_port",),

    ("items_comb_2","version_register",),
    ("items_comb_2","version_register","16_output_ports",),
    ("items_comb_2","version_register","1_output_port",),
    ("items_comb_2","version_simple",),
    ("items_comb_2","version_simple","16_output_ports",),
    ("items_comb_2","version_simple","1_output_port",),
    ("items_comb_2","16_output_ports",),
    ("items_comb_2","1_output_port",),

    ("bus_comb_1","version_register",),
    ("bus_comb_1","version_register","16_output_ports",),
    ("bus_comb_1","version_register","1_output_port",),
    ("bus_comb_1","version_simple",),
    ("bus_comb_1","version_simple","16_output_ports",),
    ("bus_comb_1","version_simple","1_output_port",),
    ("bus_comb_1","16_output_ports",),
    ("bus_comb_1","1_output_port",),

    ("bus_comb_1","items_comb_1","version_register",),
    ("bus_comb_1","items_comb_1","version_register","16_output_ports",),
    ("bus_comb_1","items_comb_1","version_register","1_output_port",),
    ("bus_comb_1","items_comb_1","version_simple",),
    ("bus_comb_1","items_comb_1","version_simple","16_output_ports",),
    ("bus_comb_1","items_comb_1","version_simple","1_output_port",),
    ("bus_comb_1","items_comb_1","16_output_ports",),
    ("bus_comb_1","items_comb_1","1_output_port",),

    ("bus_comb_1","items_comb_2","version_register",),
    ("bus_comb_1","items_comb_2","version_register","16_output_ports",),
    ("bus_comb_1","items_comb_2","version_register","1_output_port",),
    ("bus_comb_1","items_comb_2","version_simple",),
    ("bus_comb_1","items_comb_2","version_simple","16_output_ports",),
    ("bus_comb_1","items_comb_2","version_simple","1_output_port",),
    ("bus_comb_1","items_comb_2","16_output_ports",),
    ("bus_comb_1","items_comb_2","1_output_port",),

    ("bus_comb_2","version_register",),
    ("bus_comb_2","version_register","16_output_ports",),
    ("bus_comb_2","version_register","1_output_port",),
    ("bus_comb_2","version_simple",),
    ("bus_comb_2","version_simple","16_output_ports",),
    ("bus_comb_2","version_simple","1_output_port",),
    ("bus_comb_2","16_output_ports",),
    ("bus_comb_2","1_output_port",),

    ("bus_comb_2","items_comb_1","version_register",),
    ("bus_comb_2","items_comb_1","version_register","16_output_ports",),
    ("bus_comb_2","items_comb_1","version_register","1_output_port",),
    ("bus_comb_2","items_comb_1","version_simple",),
    ("bus_comb_2","items_comb_1","version_simple","16_output_ports",),
    ("bus_comb_2","items_comb_1","version_simple","1_output_port",),
    ("bus_comb_2","items_comb_1","16_output_ports",),
    ("bus_comb_2","items_comb_1","1_output_port",),

    ("bus_comb_2","items_comb_2","version_register",),
    ("bus_comb_2","items_comb_2","version_register","16_output_ports",),
    ("bus_comb_2","items_comb_2","version_register","1_output_port",),
    ("bus_comb_2","items_comb_2","version_simple",),
    ("bus_comb_2","items_comb_2","version_simple","16_output_ports",),
    ("bus_comb_2","items_comb_2","version_simple","1_output_port",),
    ("bus_comb_2","items_comb_2","16_output_ports",),
    ("bus_comb_2","items_comb_2","1_output_port",),
    ),
}
