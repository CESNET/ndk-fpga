# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "8",
        "OUT_META_MODE"   : "0",
        "UNPACKING_STAGES" : "10",
    },
    "2_regions"          : {
        "MFB_REGIONS"     : "2",
    },
    "4_regions"          : {
        "MFB_REGIONS"     : "4",
    },
    "region_size_2"      : {
        "MFB_REGION_SIZE" : "2",
    },
    "region_size_4"      : {
        "MFB_REGION_SIZE" : "4",
    },
    "out_meta_mode_eof"  : {
        "OUT_META_MODE"   : "1",
    },
    "out_meta_mode_mvb"  : {
        "OUT_META_MODE"   : "2",
    },
    "unpacking_stages_1"  : {
        "UNPACKING_STAGES" : "1",
    },
    "unpacking_stages_20" : {
        "UNPACKING_STAGES" : "20",
    },
    "_combinations_" : (
    (                                                                        ), # default
    (             "region_size_2",                                           ),
    (             "region_size_4",                                           ),
    (                              "out_meta_mode_eof",                      ),
    (             "region_size_2", "out_meta_mode_eof",                      ),
    (             "region_size_4", "out_meta_mode_eof",                      ),
    (                              "out_meta_mode_mvb",                      ),
    (             "region_size_2", "out_meta_mode_mvb",                      ),
    (             "region_size_4", "out_meta_mode_mvb",                      ),

    # STAGES
    (                                                   "unpacking_stages_20",),
    (             "region_size_2",                      "unpacking_stages_20",),
    (             "region_size_4",                      "unpacking_stages_20",),
    # (                              "out_meta_mode_eof", "unpacking_stages_20",),
    # (             "region_size_2", "out_meta_mode_eof", "unpacking_stages_20",),
    # (             "region_size_4", "out_meta_mode_eof", "unpacking_stages_20",),
    # (                              "out_meta_mode_mvb", "unpacking_stages_20",),
    # (             "region_size_2", "out_meta_mode_mvb", "unpacking_stages_20",),
    # (             "region_size_4", "out_meta_mode_mvb", "unpacking_stages_20",),

    (                                                   "unpacking_stages_1", ),
    (             "region_size_2",                      "unpacking_stages_1", ),
    (             "region_size_4",                      "unpacking_stages_1", ),
    # (                              "out_meta_mode_eof", "unpacking_stages_1", ),
    # (             "region_size_2", "out_meta_mode_eof", "unpacking_stages_1", ),
    # (             "region_size_4", "out_meta_mode_eof", "unpacking_stages_1", ),
    # (                              "out_meta_mode_mvb", "unpacking_stages_1", ),
    # (             "region_size_2", "out_meta_mode_mvb", "unpacking_stages_1", ),
    # (             "region_size_4", "out_meta_mode_mvb", "unpacking_stages_1", ),

    ("2_regions",                                                            ),
    ("2_regions", "region_size_2",                                           ),
    ("2_regions", "region_size_4",                                           ),
    ("4_regions",                                                            ),
    ("4_regions", "region_size_2",                                           ),
    ("4_regions", "region_size_4",                                           ),
    ("4_regions",                  "out_meta_mode_eof",                      ),
    ("4_regions", "region_size_2", "out_meta_mode_eof",                      ),
    ("4_regions", "region_size_4", "out_meta_mode_eof",                      ),
    ("4_regions",                  "out_meta_mode_mvb",                      ),
    ("4_regions", "region_size_2", "out_meta_mode_mvb",                      ),
    ("4_regions", "region_size_4", "out_meta_mode_mvb",                      ),

    # STAGES
    # ("2_regions",                                       "unpacking_stages_20",),
    # ("2_regions", "region_size_2",                      "unpacking_stages_20",),
    # ("2_regions", "region_size_4",                      "unpacking_stages_20",),
    ("4_regions",                                       "unpacking_stages_20",),
    ("4_regions", "region_size_2",                      "unpacking_stages_20",),
    ("4_regions", "region_size_4",                      "unpacking_stages_20",),
    # ("4_regions",                  "out_meta_mode_eof", "unpacking_stages_20",),
    # ("4_regions", "region_size_2", "out_meta_mode_eof", "unpacking_stages_20",),
    # ("4_regions", "region_size_4", "out_meta_mode_eof", "unpacking_stages_20",),
    # ("4_regions",                  "out_meta_mode_mvb", "unpacking_stages_20",),
    # ("4_regions", "region_size_2", "out_meta_mode_mvb", "unpacking_stages_20",),
    # ("4_regions", "region_size_4", "out_meta_mode_mvb", "unpacking_stages_20",),

    # ("2_regions",                                       "unpacking_stages_1", ),
    # ("2_regions", "region_size_2",                      "unpacking_stages_1", ),
    # ("2_regions", "region_size_4",                      "unpacking_stages_1", ),
    ("4_regions",                                       "unpacking_stages_1", ),
    ("4_regions", "region_size_2",                      "unpacking_stages_1", ),
    ("4_regions", "region_size_4",                      "unpacking_stages_1", ),
    # ("4_regions",                  "out_meta_mode_eof", "unpacking_stages_1", ),
    # ("4_regions", "region_size_2", "out_meta_mode_eof", "unpacking_stages_1", ),
    # ("4_regions", "region_size_4", "out_meta_mode_eof", "unpacking_stages_1", ),
    # ("4_regions",                  "out_meta_mode_mvb", "unpacking_stages_1", ),
    # ("4_regions", "region_size_2", "out_meta_mode_mvb", "unpacking_stages_1", ),
    # ("4_regions", "region_size_4", "out_meta_mode_mvb", "unpacking_stages_1", ),
    ),
}
