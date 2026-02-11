//-- ndk_macros.sv: Definition of commonly used macros
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`define ndk_override_params(CLASS_ORIG, CLASS_NEW, PARAMS, PATH, COMPONENT = null) \
    CLASS_ORIG PARAMS ::type_id::set_inst_override( CLASS_NEW PARAMS ::get_type(), PATH, COMPONENT);


