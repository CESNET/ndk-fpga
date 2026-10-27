# ver_settings.py: generics of the cocotb bench of HBM_TESTER
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

SETTINGS = {
    # HBM_TESTER indexes its counter registers with MI_ADDR(8 downto 4), so the bench keeps that field below PORTS.
    "default": {
        "PORTS": "4",
        "AXI_DATA_WIDTH": "256",
        "CNT_WIDTH": "14",
    },
}
