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
class sequence_item #(string DEVICE) extends uvm_sequence_item;
    // Registration of object tools.
    `uvm_object_param_utils(uvm_ptc_info_rc::sequence_item #(DEVICE))

    parameter DMA_COMPLETION_LENGTH_W    = 11;
    parameter DMA_REQUEST_GLOBAL_W       = 32;
    parameter DMA_REQUEST_RELAXED_W      = 1;
    parameter DMA_REQUEST_TAG_W          = 8;
    parameter DMA_COMPLETION_UNITID_W    = 8;
    parameter LEN_WIDTH                  = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 10 : 11; // 10 for INTEL 11 XILINX
    parameter LOW_ADDR_WIDTH             = (DEVICE == "STRATIX10" || DEVICE == "AGILEX") ? 7 : 12; // 7 for INTEL 12 XILINX

    // -----------------------
    // Variables.
    // -----------------------

        rand logic [DMA_REQUEST_GLOBAL_W-1 : 0]    global_id;
        rand logic [2-1 : 0]                       padd_1;
        rand logic [(DMA_REQUEST_TAG_W + 8)-1 : 0] req_id; // requester ID |vfid|"00000000"(MSB)|
        rand logic [DMA_REQUEST_TAG_W-1 : 0]       tag; // tag
        rand logic [4-1 : 0]                       lastbe; // last byte enable
        rand logic [4-1 : 0]                       firstbe; // first byte enable
        rand logic [3-1 : 0]                       fmt; // Request type |0|read_write|hdr_type ('1' for 4DWORD '0' for 3DWORD)
        rand logic [5-1 : 0]                       type_n;
        rand logic [1-1 : 0]                       tag_9;
        rand logic [3-1 : 0]                       tc; // Traffic Class
        rand logic [1-1 : 0]                       tag_8;
        rand logic [3-1 : 0]                       padd_0;
        rand logic [1-1 : 0]                       td; // ECRC
        rand logic [1-1 : 0]                       ep; // Poisoned request
        rand logic [DMA_REQUEST_RELAXED_W-1 : 0]   relaxed; // Relaxed bit
        rand logic [1-1 : 0]                       snoop; // Snoop bit
        rand logic [2-1 : 0]                       at;
        rand logic [LEN_WIDTH-1 : 0]               len; // LSB (Paket size in DWORD)
        // Others
        rand logic [LOW_ADDR_WIDTH-1 : 0]          low_addr; // LSB (Paket size in DWORD)

    // Constructor - creates new instance of this class
    function new(string name = "sequence_item");
        super.new(name);
    endfunction

    // -----------------------
    // Common UVM functions.
    // -----------------------

    // Properly copy all transaction attributes.
    function void do_copy(uvm_object rhs);
        sequence_item #(DEVICE) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal( "do_copy:", "Failed to cast transaction object.")
            return;
        end
        // Now copy all attributes
        super.do_copy(rhs);
        global_id = rhs_.global_id;
        padd_1    = rhs_.padd_1;
        req_id    = rhs_.req_id;
        tag       = rhs_.tag;
        lastbe    = rhs_.lastbe;
        firstbe   = rhs_.firstbe;
        fmt       = rhs_.fmt;
        type_n    = rhs_.type_n;
        tag_9     = rhs_.tag_9;
        tc        = rhs_.tc;
        tag_8     = rhs_.tag_8;
        padd_0    = rhs_.padd_0;
        td        = rhs_.td;
        ep        = rhs_.ep;
        relaxed   = rhs_.relaxed;
        snoop     = rhs_.snoop;
        at        = rhs_.at;
        len       = rhs_.len;
        low_addr  = rhs_.low_addr;
    endfunction: do_copy

    // Properly compare all transaction attributes representing output pins.
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit ret;
        sequence_item #(DEVICE) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        ret  = super.do_compare(rhs, comparer);
        ret &= (global_id == rhs_.global_id);
        ret &= (padd_1    == rhs_.padd_1);
        ret &= (req_id    == rhs_.req_id);
        ret &= (tag       == rhs_.tag);
        ret &= (lastbe    == rhs_.lastbe);
        ret &= (firstbe   == rhs_.firstbe);
        ret &= (fmt       == rhs_.fmt);
        ret &= (type_n    == rhs_.type_n);
        ret &= (tag_9     == rhs_.tag_9);
        ret &= (tc        == rhs_.tc);
        ret &= (tag_8     == rhs_.tag_8);
        ret &= (padd_0    == rhs_.padd_0);
        ret &= (td        == rhs_.td);
        ret &= (ep        == rhs_.ep);
        ret &= (relaxed   == rhs_.relaxed);
        ret &= (snoop     == rhs_.snoop);
        ret &= (at        == rhs_.at);
        ret &= (len       == rhs_.len);
        ret &= (low_addr  == rhs_.low_addr);
        return ret;
    endfunction: do_compare

    // Convert transaction into human readable form.
    function string convert2string();
        string ret;


        ret = $sformatf("\tglobal_id : %h\n\tpadd_1 : %b\n\treq_id : %b\n\ttag : %d\n\tlastbe : %b\n\tfirstbe : %b\n\tfmt : %b\n\ttype_n : %b\n\ttag_9 : %b\n\ttc : %b\n\ttag_8 : %b\n\tpadd_0 : %b
                      \n\ttd : %b\n\tep : %b\n\trelaxed : %b\n\tsnoop : %b\n\tat : %b\n\tlen : %d\n\tlow_addr : %h\n",
                     global_id, padd_1, req_id, tag, lastbe, firstbe, fmt,
                     type_n, tag_9, tc, tag_8, padd_0, td, ep, relaxed, snoop,
                     at, len, low_addr);

        return ret;
    endfunction
endclass

