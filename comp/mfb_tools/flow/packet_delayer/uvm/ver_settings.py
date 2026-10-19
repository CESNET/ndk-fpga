# ver_settings.py: multi-variant verification settings for MFB_PACKET_DELAYER (UVM)
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Alena Drlickova <drlickova@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # Default setting - applied on top of every combination.
    "default": {
        # MFB geometry
        "REGIONS":         "1",
        "REGION_SIZE":     "8",
        "BLOCK_SIZE":      "8",
        "ITEM_WIDTH":      "8",
        "META_WIDTH":      "16",
        "TS_WIDTH":        "16",
        # Timestamp format (0 = relative/incremental, 1 = absolute)
        "TS_FORMAT":       "0",
        # RX/TX FIFO sizing and almost-flag offsets
        "FIFO_DEPTH":      "2048",
        "FIFO_AF_OFFSET":  "1000",
        "FIFO_AE_OFFSET":  "1000",
        # Test selection (passed as CORE_PARAMS=UVM_TEST=...)
        "__core_params__": {"UVM_TEST": "test::delay_test"},
    },

    #################################################
    # MFB geometry variants
    #################################################
    "regions_2": {
        "REGIONS":         "2",
    },
    "region_size_2": {
        "REGION_SIZE":     "2",
    },
    "block_size_4": {
        "BLOCK_SIZE":      "4",
    },
    # Keep region_size*block_size within a single MFB word; widen the item only.
    "item_width_16": {
        "ITEM_WIDTH":      "16",
    },
    "item_width_32": {
        "ITEM_WIDTH":      "32",
    },
    "meta_width_8": {
        "META_WIDTH":      "8",
    },
    "ts_width_32": {
        "TS_WIDTH":        "32",
    },

    #################################################
    # Timestamp format
    #################################################
    "ts_format_1": {
        "TS_FORMAT":       "1",
    },

    #################################################
    # FIFO sizing / almost-flag hysteresis
    #################################################
    # Smaller FIFO: fills and drains much faster (good for the almost-full test).
    "fifo_small": {
        "FIFO_DEPTH":      "512",
        "FIFO_AF_OFFSET":  "256",
        "FIFO_AE_OFFSET":  "256",
    },
    # Wider hysteresis band (AFULL ~ 548 stored, AEMPTY <= 500 stored).
    "fifo_offsets_shift": {
        "FIFO_AF_OFFSET":  "1500",
        "FIFO_AE_OFFSET":  "500",
    },

    #################################################
    # Tests
    #################################################
    # Bit-exact delayer test driven by the timestamp schedule (default test).
    "test_delay": {
        "__core_params__": {"UVM_TEST": "test::delay_test"},
    },
    # Phase A almost-full/almost-empty flood test: fills the RX FIFO until
    # PAUSE_REQUEST rises (FIFO_AFULL) and drains until it falls (FIFO_AEMPTY);
    # checks bit-exact data/meta integrity with the time check disabled.
    "test_afull": {
        "__core_params__": {"UVM_TEST": "test::afull_test"},
    },
    # Two traffic phases around a TIME_RESET pulse (requires TS_FORMAT = 1).
    "test_time_reset": {
        "__core_params__": {"UVM_TEST": "test::time_reset_test"},
    },

    #################################################
    # Combinations
    #################################################
    # The "default" setting is merged into every combination, so each entry below
    # only lists the deltas. Geometry-only combinations run test::delay_test;
    # combinations that add "test_afull" run the almost-full flood test and
    # those that add "test_time_reset" the TIME_RESET test (TS_FORMAT = 1).
    "_combinations_": {
        # --- delay_test across geometry / FIFO / timestamp-format variants ---
        "delay_default":          (),
        "delay_regions_2":        ("regions_2",),
        "delay_region_size_2":    ("region_size_2",),
        "delay_block_size_4":     ("block_size_4",),
        "delay_item_width_16":    ("item_width_16",),
        "delay_item_width_32":    ("item_width_32",),
        "delay_meta_width_8":     ("meta_width_8",),
        "delay_ts_width_32":      ("ts_width_32",),
        "delay_ts_format_1":      ("ts_format_1",),
        "delay_regions_2_ts_format_1": ("regions_2", "ts_format_1"),
        "delay_fifo_small":       ("fifo_small",),
        "delay_fifo_offsets":     ("fifo_offsets_shift",),

        # --- afull_test (test::afull_test) ---
        "afull_default":          ("test_afull",),
        "afull_fifo_small":       ("test_afull", "fifo_small"),
        "afull_fifo_offsets":     ("test_afull", "fifo_offsets_shift"),
        "afull_region_size_2":    ("test_afull", "region_size_2"),
        "afull_item_width_16":    ("test_afull", "item_width_16"),
        "afull_ts_format_1":      ("test_afull", "ts_format_1"),

        # --- time_reset_test (test::time_reset_test, TS_FORMAT = 1 only) ---
        "time_reset_ts_format_1":           ("test_time_reset", "ts_format_1"),
        "time_reset_regions_2_ts_format_1": ("test_time_reset", "ts_format_1", "regions_2"),
    },
}
