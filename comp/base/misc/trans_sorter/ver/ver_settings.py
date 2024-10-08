# ver_settings.py : Setting for MultiVer script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "TS_ID_WIDTH"           : "5" ,
        "TS_META_WIDTH"         : "1" ,
        "TS_BEHAVIOUR"          : "0" ,
        "MAX_SAME_ID"           : "1" ,
        "FIFOX_SHAKEDOWN_MODE"  : "0" ,
        "MAX_RX_TRANS"          : "2" ,
        "MAX_TX_TRANS"          : "2" ,
        "MAX_ID_CONFS"          : "2" ,
    },
    "wide_transaction" : {
        "TS_ID_WIDTH"           : "8" ,
        "TS_META_WIDTH"         : "5" ,
    },
    "one_IO_interfaces": {
        "MAX_RX_TRANS"          : "1" ,
        "MAX_TX_TRANS"          : "1" ,
        "MAX_ID_CONFS"          : "1" ,
    },
    "multiple_IO_interfaces": {
        "MAX_RX_TRANS"          : "6" ,
        "MAX_TX_TRANS"          : "4" ,
        "MAX_ID_CONFS"          : "3" ,
    },
    "shakedown" : {
        "FIFOX_SHAKEDOWN_MODE"  : "1" ,
    },
    "behaviour" : {
        "TS_BEHAVIOUR"          : "1" ,
    },
    "3_same_id" : {
        "MAX_SAME_ID"           : "3" ,
    },
    "_combinations_" : (
    (),
        ("wide_transaction",                                                          ),
        (                   "one_IO_interfaces",                                      ),
        ("wide_transaction","one_IO_interfaces",                                      ),
        (                                        "multiple_IO_interfaces",            ),
        ("wide_transaction",                     "multiple_IO_interfaces",            ),
        (                                                                 "shakedown",),
        ("wide_transaction",                                              "shakedown",),
        (                   "one_IO_interfaces",                          "shakedown",),
        ("wide_transaction","one_IO_interfaces",                          "shakedown",),
        (                                        "multiple_IO_interfaces","shakedown",),
        ("wide_transaction",                     "multiple_IO_interfaces","shakedown",),
    ),
}
