# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
        "FAKE_PIPE"         : "0",
        "USE_DST_RDY"       : "1",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "64",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_3" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "ITEMS"             : "8",
    },
    "items_comb_2" : {
        "ITEMS"             : "1",
    },
    "use_dst_rdy_0" : {
        "USE_DST_RDY"       : "0",
    },
    "fake_pipe_1" : {
        "FAKE_PIPE"         : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("use_dst_rdy_0",),
    ("fake_pipe_1",),
    ("bus_comb_1",),
    ("bus_comb_1","fake_pipe_1",),
    ("bus_comb_1","use_dst_rdy_0",),
    ("bus_comb_1","fake_pipe_1",),
    ("bus_comb_2",),
    ("bus_comb_2","fake_pipe_1",),
    ("bus_comb_2","use_dst_rdy_0",),
    ("bus_comb_2","fake_pipe_1",),
    ("bus_comb_3",),
    ("bus_comb_3","fake_pipe_1",),
    ("bus_comb_3","use_dst_rdy_0",),
    ("bus_comb_3","fake_pipe_1",),

    ("items_comb_1",),
    ("items_comb_1","use_dst_rdy_0",),
    ("items_comb_1","fake_pipe_1",),
    ("items_comb_1","bus_comb_1",),
    ("items_comb_1","bus_comb_1","fake_pipe_1",),
    ("items_comb_1","bus_comb_1","use_dst_rdy_0",),
    ("items_comb_1","bus_comb_1","fake_pipe_1",),
    ("items_comb_1","bus_comb_2",),
    ("items_comb_1","bus_comb_2","fake_pipe_1",),
    ("items_comb_1","bus_comb_2","use_dst_rdy_0",),
    ("items_comb_1","bus_comb_2","fake_pipe_1",),
    ("items_comb_1","bus_comb_3",),
    ("items_comb_1","bus_comb_3","fake_pipe_1",),
    ("items_comb_1","bus_comb_3","use_dst_rdy_0",),
    ("items_comb_1","bus_comb_3","fake_pipe_1",),

    ("items_comb_2",),
    ("items_comb_2","use_dst_rdy_0",),
    ("items_comb_2","fake_pipe_1",),
    ("items_comb_2","bus_comb_1","fake_pipe_1",),
    ("items_comb_2","bus_comb_1","use_dst_rdy_0",),
    ("items_comb_2","bus_comb_1","fake_pipe_1",),
    ("items_comb_2","bus_comb_2","fake_pipe_1",),
    ("items_comb_2","bus_comb_2","use_dst_rdy_0",),
    ("items_comb_2","bus_comb_2","fake_pipe_1",),
    ("items_comb_2","bus_comb_3","fake_pipe_1",),
    ("items_comb_2","bus_comb_3","use_dst_rdy_0",),
    ("items_comb_2","bus_comb_3","fake_pipe_1",),
    ),
}
