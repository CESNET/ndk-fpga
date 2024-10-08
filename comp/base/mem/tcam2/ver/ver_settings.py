# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "DATA_WIDTH"             : "8"                  ,
        "ITEMS"                  : "64"                 ,
        "RESOURCES_SAVING"       : "0"                  ,
        "WRITE_BEFORE_MATCH"     : "TRUE"               ,
        "READ_FROM_TCAM"         : "TRUE"               ,
        "OUTPUT_READ_REGS"       : "TRUE"               ,
        "USE_FRAGMENTED_MEM"     : "FALSE"              ,
        "DEVICE"                 : "\\\"ULTRASCALE\\\"" ,

        "WRITE_COUNT"            : "200"                ,
        "MATCH_COUNT"            : "100000"             ,
        "READ_COUNT"             : "200"                ,
    },
    "16b_data" : { #
        "DATA_WIDTH"             : "16"                 ,
    },
    "32b_data" : { #
        "DATA_WIDTH"             : "32"                 ,
    },
    "128_storage" : { #
        "ITEMS"                  : "128"                ,
    },
    "256_storage" : { #
        "ITEMS"                  : "256"                ,
    },
    "RS_1" : { #
        "RESOURCES_SAVING"      : "1"                   ,
    },
    "RS_2" : { #
        "RESOURCES_SAVING"      : "2"                   ,
    },
    "match_priority" : { #
        "WRITE_BEFORE_MATCH"     : "FALSE"              ,
    },
    "no_read" : { #
        "READ_FROM_TCAM"         : "FALSE"              ,
    },
    "no_read_regs" : { #
        "OUTPUT_READ_REGS"       : "FALSE"              ,
    },
    "intel_tcam" : { #
        "DEVICE"                 : "\\\"STRATIX10\\\""  ,
    },
    "intel_frag_mem" : { #
        "USE_FRAGMENTED_MEM"     : "TRUE"  ,
    },
#    "" : { #
#    },
    "_combinations_" : (
    # basic tests
    ("default"          ,),
    ("16b_data"         ,),
    #("32b_data"         ,),
    ("128_storage"      ,),
    #("256_storage"      ,),
    ("RS_1"             ,),
    ("RS_2"             ,),
    ("match_priority"   ,),
    ("no_read"          ,),
    #("no_read_regs"     ,),
    ("intel_tcam"       ,),

    # XILINX larger storage
    ("16b_data", "128_storage"                    ,),
    # XILINX larger storage with RS_1
    ("16b_data", "128_storage", "RS_1"            ,),
    # XILINX large storage with RS_2
    #("32b_data", "256_storage", "RS_2"            ,),
    # XILINX large storage with RS_2 without read
    #("32b_data", "256_storage", "RS_2", "no_read" ,),

    # INTEL fragmented memory
    ("intel_tcam", "intel_frag_mem"    ,),

    # INTEL larger storage
    ("intel_tcam", "16b_data", "128_storage"                                        ,),
    ("intel_tcam", "16b_data", "128_storage", "intel_frag_mem"                      ,),
    # INTEL larger storage with RS_1
    ("intel_tcam", "16b_data", "128_storage", "RS_1"                                ,),
    ("intel_tcam", "16b_data", "128_storage", "RS_1", "intel_frag_mem"              ,),
    # INTEL large storage with RS_2
    #("intel_tcam", "32b_data", "256_storage", "RS_2"                                ,),
    #("intel_tcam", "32b_data", "256_storage", "RS_2", "intel_frag_mem"              ,),
    # INTEL large storage with RS_2 without read
    #("intel_tcam", "32b_data", "256_storage", "RS_2", "no_read"                     ,),
    #("intel_tcam", "32b_data", "256_storage", "RS_2", "no_read", "intel_frag_mem"   ,),


    #
    #(,)
    )
}
