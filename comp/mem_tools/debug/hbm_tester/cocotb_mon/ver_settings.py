# ver_settings.py: generics of the cocotb bench of HBM_TESTER_MON
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

SETTINGS = {
    # Narrow counters reach their saturation in a short window; the bench reads the width from the ports.
    "default": {
        "CNT_WIDTH": "8",
    },
}
