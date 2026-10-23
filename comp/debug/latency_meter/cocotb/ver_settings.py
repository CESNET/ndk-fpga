# ver_settings.py: generic combinations of the LATENCY_METER cocotb test
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

SETTINGS = {
    # The default setting of verification. Only changed generics are listed.
    "default": {
        "DATA_WIDTH": "16",
        "MAX_PARALEL_EVENTS": "8",
        "START_META_WIDTH": "4",
        "END_META_WIDTH": "4",
    },

    "narrow_counter": {
        "DATA_WIDTH": "6",
        "MAX_PARALEL_EVENTS": "4",
        "START_META_WIDTH": "1",
        "END_META_WIDTH": "1",
    },

    "deep_fifo": {
        "DATA_WIDTH": "32",
        "MAX_PARALEL_EVENTS": "64",
        "START_META_WIDTH": "8",
        "END_META_WIDTH": "3",
    },

    "_combinations_": (
        (),
        ("narrow_counter",),
        ("deep_fifo",),
    ),
}
