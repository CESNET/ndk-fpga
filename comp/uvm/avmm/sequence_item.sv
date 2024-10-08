// sequence_item.sv: Item for AVMM sequencer
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Request
class sequence_item_request #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_avmm::sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Bus structure of AVMM
    rand logic                       ready;
    rand logic                       read;
    rand logic                       write;
    rand logic [ADDRESS_WIDTH-1 : 0] address;
    rand logic [DATA_WIDTH   -1 : 0] writedata;
    rand logic [BURST_WIDTH  -1 : 0] burstcount;

    constraint c_read_write { !(read == 1'b1 && write == 1'b1); }
    constraint c_burstcount { !(burstcount == 0); }

    // Constructor
    function new(string name = "sequence_item_request");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copies all attributes
        super.do_copy(rhs);
        ready         = rhs_.ready;
        read          = rhs_.read;
        write         = rhs_.write;
        address       = rhs_.address;
        writedata     = rhs_.writedata;
        burstcount    = rhs_.burstcount;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compares all attributes that maters
        return (
            (super.do_compare(rhs, comparer))   &&
            (ready         === rhs_.ready)      &&
            (read          === rhs_.read)       &&
            (write         === rhs_.write)      &&
            (address       === rhs_.address)    &&
            (writedata     === rhs_.writedata)  &&
            (burstcount    === rhs_.burstcount)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tREQUEST:\n\tREADY: %0b \n\tREAD: %0b \n\tWRITE: %0b \n\tADDRESS: %0h \n\tWRITEDATA: %0h \n\tBURSTCOUNT: %0d \n",
                            ready,
                            read,
                            write,
                            address,
                            writedata,
                            burstcount
                        );

        return output_string;
    endfunction

endclass

// Response
class sequence_item_response #(int unsigned DATA_WIDTH) extends uvm_common::sequence_item;
    `uvm_object_param_utils(uvm_avmm::sequence_item_response #(DATA_WIDTH))

    // Bus structure of AVMM
    rand logic                    ready;
    rand logic [DATA_WIDTH-1 : 0] readdata;
    rand logic                    readdatavalid;

    // Constructor
    function new(string name = "sequence_item_response");
        super.new(name);
    endfunction

    // -------------------- //
    // Common UVM functions //
    // -------------------- //

    // Properly copies all transaction attributes
    function void do_copy(uvm_object rhs);
        sequence_item_response #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_copy:", "Failed to cast transaction object.")
            return;
        end

        // Copies all attributes
        super.do_copy(rhs);
        ready         = rhs_.ready;
        readdata      = rhs_.readdata;
        readdatavalid = rhs_.readdatavalid;
    endfunction

    // Properly compares all transaction attributes representing output pins
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        sequence_item_response #(DATA_WIDTH) rhs_;

        if(!$cast(rhs_, rhs)) begin
            `uvm_fatal("do_compare:", "Failed to cast transaction object.")
            return 0;
        end

        // Compares all attributes that maters
        return (
            (super.do_compare(rhs, comparer))      &&
            (ready         === rhs_.ready)         &&
            (readdata      === rhs_.readdata)      &&
            (readdatavalid === rhs_.readdatavalid)
        );
    endfunction

    // Visualize the sequence item to string
    function string convert2string();
        string output_string;

        output_string = $sformatf("\n\tRESPONSE:\n\tREADY: %0b \n\tREADDATA %0h \n\tREADDATAVALID %0b \n",
                            ready,
                            readdata,
                            readdatavalid
                        );

        return output_string;
    endfunction

endclass
