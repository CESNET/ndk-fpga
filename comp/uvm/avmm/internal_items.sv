// internal_items.sv: Request and response items
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Request
class request_item #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_avmm::request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    request_item_type_e         request_type;
    logic [ADDRESS_WIDTH-1 : 0] address;
    logic [DATA_WIDTH   -1 : 0] writedata;
    logic [BURST_WIDTH  -1 : 0] burstcount;

    // Constructor
    function new(string name = "request_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copies all attributes
        super.do_copy(rhs);
        request_type = rhs_.request_type;
        address      = rhs_.address;
        writedata    = rhs_.writedata;
        burstcount   = rhs_.burstcount;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compares all attributes that maters
        return (
            (super.do_compare(rhs, comparer))    &&
            (request_type === rhs_.request_type) &&
            (address      === rhs_.address)      &&
            (writedata    === rhs_.writedata)    &&
            (burstcount   === rhs_.burstcount)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tREQUEST ITEM:\n\tTYPE: %s \n\tADDRESS: %0h \n\tWRITEDATA: %0h \n\tBURSTCOUNT: %0d \n",
                            request_type.name(),
                            address,
                            writedata,
                            burstcount
                        );

        return output_string;
    endfunction

endclass

// Response
class response_item #(int unsigned DATA_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_avmm::response_item #(DATA_WIDTH))

    logic [DATA_WIDTH-1 : 0] readdata;
    time timestamp;

    // Constructor
    function new(string name = "response_item");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        response_item #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copies all attributes
        super.do_copy(rhs);
        readdata  = rhs_.readdata;
        timestamp = rhs_.timestamp;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        response_item #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compares all attributes that maters
        return (
            (super.do_compare(rhs, comparer)) &&
            (readdata  === rhs_.readdata)      &&
            (timestamp === rhs_.timestamp)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tRESPONSE ITEM:\n\tREADDATA: %0h \n",
                            readdata
                        );

        return output_string;
    endfunction

endclass
