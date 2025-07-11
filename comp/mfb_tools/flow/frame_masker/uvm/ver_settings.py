# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"        : "4",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "8",
        "MFB_META_WIDTH"     : "16",
        "USE_PIPE"           : "0",
        "FRAME_SIZE_MIN"     : "60",
        "FRAME_SIZE_MAX"     : "1500",
    },
    "pcie" : {
        "MFB_REGIONS"        : "2",
        "MFB_REGION_SIZE"    : "1",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "32",
    },
    "one_region" : {
        "MFB_REGIONS"        : "1",
    },
    "pipe_enabled" : {
        "USE_PIPE"           : "1",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"     : "1500",
        "FRAME_SIZE_MAX"     : "5000",
        "MFB_META_WIDTH"     : "31",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "32",
        "FRAME_SIZE_MAX"     : "100",
        "MFB_META_WIDTH"     : "5",
    },
    "uvm_speed_test" : {
        "__core_params__" : {"UVM_TEST": "test::speed"}
    },
    "uvm_all_pass_test" : {
        "__core_params__" : {"UVM_TEST": "test::test_all_pass"}
    },
    "uvm_all_pass_and_one_frame_test" : {
        "__core_params__" : {"UVM_TEST": "test::test_all_pass_and_one_frame"}
    },
    "_combinations_" : (
    (                                                                                ), # Works the same as '("default",),' as the "default" is applied in every combination
    ("pcie"      ,                                 "uvm_speed_test",                 ),
    ("one_region",                                 "uvm_all_pass_test",              ),
    ("one_region", "pipe_enabled",                 "uvm_all_pass_and_one_frame_test",),
    ("pcie"      , "pipe_enabled",                                                   ),
    (              "pipe_enabled",                 "uvm_speed_test",                 ),
    (                              "big_frames",   "uvm_all_pass_test",              ),
    ("pcie"      ,                 "big_frames",   "uvm_all_pass_and_one_frame_test",),
    ("one_region",                 "big_frames",                                     ),
    ("one_region",                 "small_frames", "uvm_speed_test",                 ),
    ("pcie"      ,                 "small_frames", "uvm_all_pass_test",              ),
    (                              "small_frames", "uvm_all_pass_and_one_frame_test",),
    ),
}
