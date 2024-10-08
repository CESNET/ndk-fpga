//-- sequence.sv
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_simple #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX) extends uvm_common::sequence_base#(config_sequence, sequence_item);
    `uvm_object_param_utils(uvm_pcie_hdr::sequence_simple #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX))

    rand int unsigned      transaction_count;
    int unsigned           transaction_count_min = 10;
    int unsigned           transaction_count_max = 100;
    uvm_pcie_hdr::sync_tag tag_sync;

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple");
        super.new(name);
    endfunction

    // Generates transactions
    task body;

        tag_sync = cfg.tag_sync;

        `uvm_info(get_full_name(), "uvm_pcie_hdr::sequence_simple is running", UVM_DEBUG)
        repeat(transaction_count)
        begin
            // Generate random request
            `uvm_do_with(req, { dw_count inside {[PCIE_LEN_MIN : PCIE_LEN_MAX]};
                                if (dw_count == 1) {
                                    fbe inside {4'b1001, 4'b0101, 4'b1010, 4'b0011, 4'b0110, 4'b1100, 4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0000};
                                    lbe == 4'b0000;
                                } else {
                                    fbe inside {4'b0001, 4'b0010, 4'b0100, 4'b1000};
                                    lbe inside {4'b0001, 4'b0010, 4'b0100, 4'b1000};
                                }
                                if (IS_XILINX_DEV) {
                                    //               MEM_READ     MEM_WRITE
                                    req_type dist {8'b00000000 :/ 90, 8'b00000001 :/ 90,
                                    // Others (errors)
                                    8'b00000010 :/ 10, 8'b00000011 :/ 10, 8'b00000100 :/ 10, 8'b00000101 :/ 10, 8'b00000110 :/ 10, 8'b00000111 :/ 10, 8'b00001000 :/ 10, 8'b00001001 :/ 10, 8'b00001010 :/ 10, 8'b00001011 :/ 10, 8'b00001100 :/ 10, 8'b00001101 :/ 10, 8'b00001110 :/ 10};
                                }
                                else {
                                    // 4 DW Address
                                    if (|addr[64-1 : 32]) {
                                        //               MEM_READ     MEM_WRITE
                                        req_type dist {8'b00100000 :/ 90, 8'b01100000 :/ 90,
                                        // MSG
                                        8'b00110000 :/ 10, 8'b00110001 :/ 10, 8'b00110010 :/ 10, 8'b00110011 :/ 10, 8'b00110100 :/ 10, 8'b00110101 :/ 10,
                                        // MSGd
                                        8'b01110000 :/ 10, 8'b01110001 :/ 10, 8'b01110010 :/ 10, 8'b01110011 :/ 10, 8'b01110100 :/ 10, 8'b01110101 :/ 10,
                                        // others types Reads
                                        8'b00100001 :/ 10,
                                        // others types Writes
                                        8'b01101100 :/ 10, 8'b01101101 :/ 10, 8'b01101110 :/ 10};
                                    }
                                    // 3 DW Address
                                    else {
                                        //               MEM_READ     MEM_WRITE
                                        req_type dist {8'b00000000 :/ 90, 8'b01000000 :/ 90,
                                        //others types reads
                                        8'b00000010 :/ 10, 8'b00000100 :/ 10, 8'b00000101 :/ 10, 8'b00001010 :/ 10, 8'b00001011 :/ 10,
                                        // others types writes
                                        8'b01000010 :/ 10, 8'b01000100 :/ 10, 8'b01000101 :/ 10, 8'b01001010 :/ 10, 8'b01001011 :/ 10, 8'b01001100 :/ 10, 8'b01001101 :/ 10, 8'b01001110 :/ 10};
                                    }
                                }
                                // tph_present == '0;
                                bar inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101, 3'b110};
                                bar_ap == 6'd24;
                                // tph_type == '0;
                                // tph_st_tag == 0;
                                addr[2-1 : 0] == 2'b00;
                                if (tag_sync.list_of_tags.size() != 0) {
                                    if (req_type == 8'b00000000 || req_type == 8'b00100000){
                                        tag inside {tag_sync.list_of_tags};
                                    }
                                }
                               });
        end
    endtask
endclass

//////////////////////////////////////
// TX LIBRARY
class sequence_lib #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX) extends uvm_common::sequence_library#(config_sequence, sequence_item);
  `uvm_object_param_utils(uvm_pcie_hdr::sequence_lib #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX))
  `uvm_sequence_library_utils(uvm_pcie_hdr::sequence_lib #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX))

    function new(string name = "sequence_lib");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(sequence_simple #(IS_XILINX_DEV, PCIE_LEN_MIN, PCIE_LEN_MAX)::get_type());
    endfunction
endclass

