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


///////////////////////////////////////////////////////
// MACRO SIMPLIFY dist randomization
///////////////////////////////////////////////////////
// EXAMPLE:
//      upd_timeout dist {
//          `ndk_rand_dist_first(5, 1024, 8) :/ 10,
//          `ndk_rand_dist      (5, 1024, 8, 1)  :/ 10,
//          `ndk_rand_dist      (5, 1024, 8, 2)  :/ 8,
//          `ndk_rand_dist      (5, 1024, 8, 3)  :/ 3,
//          `ndk_rand_dist      (5, 1024, 8, 4)  :/ 1,
//          `ndk_rand_dist      (5, 1024, 8, 5)  :/ 3,
//          `ndk_rand_dist      (5, 1024, 8, 6)  :/ 8,
//          `ndk_rand_dist      (5, 1024, 8, 7)  :/ 10,
//          `ndk_rand_dist_last (5, 1024, 8) :/ 10
//      };
`define ndk_rand_dist_first(MIN, MAX, DIVIDER) \
    [MIN:MIN+((MAX-MIN)/DIVIDER)]

`define ndk_rand_dist(MIN, MAX, DIVIDER, BLOCK) \
    [MIN+((MAX-MIN)/DIVIDER)*(BLOCK-1):MIN+((MAX-MIN)/DIVIDER)*BLOCK]

`define ndk_rand_dist_last(MIN, MAX, DIVIDER) \
    [MIN+((MAX-MIN)/DIVIDER)*(DIVIDER-1):MAX]

///////////////////////////////////////////////////////
// MACRO COMPARE unpacked arrays with wildcard
///////////////////////////////////////////////////////
// Wildcard equality (==?) is not defined for unpacked arrays,
// so ndk_array_cmp_wildcard compares the arrays element by element.
// RET is AND-ed with the result (initialize it to 1'b1).
//
// In test foreach was qucker that ==?
//
// EXAMPLE:
//      bit ret = 1'b1;
//      `ndk_array_cmp_wildcard(ret, tr_dut.data, tr_model.data) // X/Z in tr_model.data match anything
`define ndk_array_cmp_wildcard(RET, ARR_A, ARR_WILDCARD) \
    begin \
        if ($size(ARR_A) != $size(ARR_WILDCARD)) begin \
            RET &= 1'b0; \
        end else begin \
            foreach (ARR_A[ndk_array_cmp_wildcard_it]) begin \
                RET &= ((ARR_A[ndk_array_cmp_wildcard_it] ==? ARR_WILDCARD[ndk_array_cmp_wildcard_it]) === 1'b1); \
            end \
        end \
    end

