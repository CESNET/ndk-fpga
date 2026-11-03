# ver_settings.py
# MVB_FORK UVM verification
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Alena Drlickova <drlickova@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "OUTPUT_PORTS"      : "2",
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
        "USE_DST_RDY"       : "1",
        "VERSION"           : "\\\"logic\\\"",
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
    "version_register_directed_test" : {
        "VERSION"           : "\\\"register\\\"",
    "__core_params__" : {"UVM_TEST": "test::directed_test_register"},
    },
    "version_simple" : {
        "VERSION"           : "\\\"simple\\\"",
    },
    "use_dst_rdy_0" : {
        "USE_DST_RDY"       : "0",
    },
    "3_output_ports" : {
        "OUTPUT_PORTS"      : "3",
    },
    "1_output_port" : {
        "OUTPUT_PORTS"      : "1",
    },
    "_combinations_" : (
    (),

    ("items_comb_1",),
    ("items_comb_2",),

    ("version_register",),
    ("version_simple",),
    ("use_dst_rdy_0",),

    ("version_register_directed_test",),

    ("version_register","use_dst_rdy_0",),
    ("version_simple","use_dst_rdy_0",),
    ("version_register","1_output_port",),
    ("version_register","3_output_ports",),
    ("version_simple","3_output_ports",),
    ("3_output_ports",),
    ("1_output_port",),

    ("items_comb_1","version_register",),
    ("items_comb_2","version_register",),
    ("items_comb_2","version_simple",),
    ),
}
