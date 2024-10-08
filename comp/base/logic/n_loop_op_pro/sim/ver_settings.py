# ver_settings.py
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "DATA_WIDTH"           : "8"              ,
        "ITEMS"                : "4"              ,
        "QUICK_RESET_EN"       : "true"           ,
        "RESET_VAL"            : "42"             ,
        "READ_PORTS"           : "8"              ,
        "OPERATORS"            : "3"              ,
        "OPERATIONS"           : "2"              ,
    },
    "many_items" : { # More Items
        "DATA_WIDTH"           : "16"             ,
        "ITEMS"                : "256"            ,
    },
    "no_quick_reset" : { #
        "QUICK_RESET_EN"       : "false"          ,
    },
    "single_port" : { #
        "READ_PORTS"           : "1"              ,
        "OPERATORS"            : "1"              ,
        "OPERATIONS"           : "1"              ,
    },
#    "" : { #
#    },
}
