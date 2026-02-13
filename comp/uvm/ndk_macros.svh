//-- ndk_macros.sv: Definition of commonly used macros
//-- Copyright (C) 2026 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`define ndk_override_params(CLASS_ORIG, CLASS_NEW, PARAMS, PATH, COMPONENT = null) \
    CLASS_ORIG PARAMS ::type_id::set_inst_override( CLASS_NEW PARAMS ::get_type(), PATH, COMPONENT);


//`define ndk_component_utils(Ttype, Tname=`"Ttype`") \
`define ndk_component_utils(Ttype) \
    `ndk_component_param_utils(Ttype, `"Ttype`")

`define ndk_component_param_utils(Ttype, Tname) \
    typedef uvm_component_registry #(Ttype, Tname) type_id; \
    static function type_id get_type(); \
        return type_id::get(); \
    endfunction \
    virtual function uvm_object_wrapper get_object_type(); \
        return type_id::get(); \
    endfunction \
    const static string type_name =  Tname; \
    virtual function string get_type_name (); \
        return Tname; \
    endfunction


//`define ndk_object_utils(Tobj, Tname=`"Tobj`") \
`define ndk_object_utils(Tobj) \
    `ndk_object_param_utils(Tobj, `"Tobj`")

`define ndk_object_param_utils(Tobj, Tname) \
    typedef uvm_object_registry#(Tobj, Tname) type_id; \
    static function type_id get_type(); \
        return type_id::get(); \
    endfunction \
    virtual function uvm_object_wrapper get_object_type(); \
        return type_id::get(); \
    endfunction \
    const static string type_name = Tname; \
    virtual function string get_type_name (); \
        return type_name; \
    endfunction \
    `m_uvm_object_create_func(Tobj) \
    `uvm_field_utils_begin(Tobj) \
    `uvm_object_utils_end

