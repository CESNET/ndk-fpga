/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_lib #(int unsigned DATA_WIDTH) extends uvm_sequence_library #(uvm_pma::sequence_item #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_pma::sequence_lib #(DATA_WIDTH))
    `uvm_sequence_library_utils(uvm_byte_array_pma::sequence_lib #(DATA_WIDTH))
    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction
    virtual function void init_sequence_rx_pcs();
        this.add_sequence(uvm_byte_array_pma::sequence_simple #(DATA_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_pma::sequence_hdr_err_inj #(DATA_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_pma::sequence_seq_err_inj #(DATA_WIDTH)::get_type());
    endfunction

endclass
