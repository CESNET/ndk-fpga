# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "INPUTS"            : "32",
        "OUTPUTS"           : "4",
        "DATA_WIDTH"        : "32",
        "OUTPUT_REG"        : "1",
        "TRANSACTION_COUNT" : "2000",
    },
    "bus_comb_1" : {
        "DATA_WIDTH"        : "8",
    },
    "bus_comb_2" : {
        "DATA_WIDTH"        : "77",
    },
    "inputs_comb_1" : {
        "INPUTS"            : "1",
    },
    "inputs_comb_2" : {
        "INPUTS"            : "8",
    },
    "inputs_comb_3" : {
        "INPUTS"            : "16",
    },
    "outputs_comb_1" : {
        "OUTPUTS"           : "1",
    },
    "outputs_comb_2" : {
        "OUTPUTS"           : "8",
    },
    "outputs_comb_3" : {
        "OUTPUTS"           : "16",
    },
    "output_reg_0" : {
        "OUTPUT_REG"        : "0",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("outputs_comb_1",),
    ("outputs_comb_2",),
    ("outputs_comb_3",),
    ("output_reg_0",),

    ("bus_comb_1",),
    ("bus_comb_1","output_reg_0",),
    ("bus_comb_1","outputs_comb_1",),
    ("bus_comb_1","outputs_comb_2",),
    ("bus_comb_1","outputs_comb_3",),

    ("bus_comb_2",),
    ("bus_comb_2","output_reg_0",),
    ("bus_comb_2","outputs_comb_1",),
    ("bus_comb_2","outputs_comb_2",),
    ("bus_comb_2","outputs_comb_3",),

    ("inputs_comb_1","outputs_comb_1",),
    ("inputs_comb_1","outputs_comb_1","output_reg_0",),
    ("inputs_comb_1","bus_comb_1","outputs_comb_1",),
    ("inputs_comb_1","bus_comb_2","outputs_comb_1",),

    ("inputs_comb_2",),
    ("inputs_comb_2","outputs_comb_1",),
    ("inputs_comb_2","outputs_comb_2",),
    ("inputs_comb_2","outputs_comb_2","output_reg_0",),

    ("inputs_comb_2","bus_comb_1",),
    ("inputs_comb_2","bus_comb_1","outputs_comb_1",),
    ("inputs_comb_2","bus_comb_1","outputs_comb_2",),

    ("inputs_comb_2","bus_comb_2",),
    ("inputs_comb_2","bus_comb_2","outputs_comb_1",),
    ("inputs_comb_2","bus_comb_2","outputs_comb_2",),

    ("inputs_comb_3",),
    ("inputs_comb_3","outputs_comb_1",),
    ("inputs_comb_3","outputs_comb_2",),
    ("inputs_comb_3","outputs_comb_3",),

    ("inputs_comb_3","bus_comb_1",),
    ("inputs_comb_3","bus_comb_1","outputs_comb_1",),
    ("inputs_comb_3","bus_comb_1","outputs_comb_2",),
    ("inputs_comb_3","bus_comb_1","outputs_comb_3",),
    ("inputs_comb_3","bus_comb_1","outputs_comb_3","output_reg_0",),

    ("inputs_comb_3","bus_comb_2",),
    ("inputs_comb_3","bus_comb_2","outputs_comb_1",),
    ("inputs_comb_3","bus_comb_2","outputs_comb_2",),
    ("inputs_comb_3","bus_comb_2","outputs_comb_3",),

    ),
}
