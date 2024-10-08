//-- pkg.sv
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// Items description
//
// ========= ==================================================================
// LENGTH    Lenght of data in current request/completion in DWORDs (4B); for read request it is a requested size
// TYPE      Request type, currently only read and write requests are supported
// FIRSTIB   First invalid bytes - specifies, how many bytes at first data word are invalid; used to generate First BE
// LASTIB    Last invalid bytes - specifies, how many bytes at last data word are invalid; used to generate Last BE
// TAG       Transaction ID unique in scope of current unit; it will be translated to an PCI tag together with UNITID
// UNITID    Transaction ID unique for each unit (in scope of 1 endpoint) and is used for routing of completions
// GLOBAL    Global 64b address to main memory space of request
// VFID      Virtual function ID for specifying PCI function
// PASID     Process Address Space ID for better granularity of virtualization
// PASIDVLD  PASID value is valid and will be used to generate TLP PASID prefix
// RELAXED   Relaxed ordering in the mean of PCIe standard; typically needs to be set in all read requests
// ========= ==================================================================


// This class represents high level transaction, which can be reusable for other components.
class sequence_item extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_utils(uvm_ptc_info::sequence_item)

    parameter DMA_REQUEST_LENGTH_W          = 11;
    parameter DMA_REQUEST_TYPE_W            = 1;
    parameter DMA_REQUEST_FIRSTIB_W         = 2;
    parameter DMA_REQUEST_LASTIB_W          = 2;
    parameter DMA_REQUEST_TAG_W             = 8;
    parameter DMA_REQUEST_UNITID_W          = 8;
    parameter DMA_REQUEST_GLOBAL_W          = 64;
    parameter DMA_REQUEST_VFID_W            = 8;
    parameter DMA_REQUEST_PASID_W           = 0;
    parameter DMA_REQUEST_PASIDVLD_W        = 0;
    parameter DMA_REQUEST_RELAXED_W         = 1;

    // -----------------------
    // Variables.
    // -----------------------

    rand logic [DMA_REQUEST_LENGTH_W-1 : 0]  length;
    rand logic [DMA_REQUEST_TYPE_W-1 : 0]    type_ide;
    rand logic [DMA_REQUEST_FIRSTIB_W-1 : 0] firstib;
    rand logic [DMA_REQUEST_LASTIB_W-1 : 0]  lastib;
    rand logic [DMA_REQUEST_TAG_W-1 : 0]     tag;
    rand logic [DMA_REQUEST_UNITID_W-1 : 0]  unitid;
    rand logic [DMA_REQUEST_GLOBAL_W-1 : 0]  global_id;
    rand logic [DMA_REQUEST_VFID_W-1 : 0]    vfid;
    rand logic                               pasid;
    rand logic                               pasidvld;
    rand logic [DMA_REQUEST_RELAXED_W-1 : 0] relaxed;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        length    = rhs_.length;
        type_ide  = rhs_.type_ide;
        firstib   = rhs_.firstib;
        lastib    = rhs_.lastib;
        tag       = rhs_.tag;
        unitid    = rhs_.unitid;
        global_id = rhs_.global_id;
        vfid      = rhs_.vfid;
        pasid     = rhs_.pasid;
        pasidvld  = rhs_.pasidvld;
        relaxed   = rhs_.relaxed;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret  = super.do_compare(rhs, comparer);
        ret &= (length    == rhs_.length);
        ret &= (type_ide  == rhs_.type_ide);
        ret &= (firstib   == rhs_.firstib);
        ret &= (lastib    == rhs_.lastib);
        ret &= (tag       == rhs_.tag);
        ret &= (unitid    == rhs_.unitid);
        ret &= (global_id == rhs_.global_id);
        ret &= (vfid      == rhs_.vfid);
        ret &= (pasid     == rhs_.pasid);
        ret &= (pasidvld  == rhs_.pasidvld);
        ret &= (relaxed   == rhs_.relaxed);
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;

        ret = $sformatf("\tLength : %d\n\tType : %b\n\tFirstIB : %0d\n\tlastIB : %0d\n\ttag : %0d(0x%h)\n\tunitid : 0x%h\n\tglobal : 0x%h\n\tvfid : 0x%h\n\tpasid : 0x%h\n\tpasidvld : %b\n\trelaxed : %b\n",
                     length, type_ide, firstib, lastib, tag, tag, unitid, global_id, vfid, pasid, pasidvld, relaxed);

        return ret;
    endfunction
endclass

