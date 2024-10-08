/*
 * file       : sequence_lib.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array to MII sequence libraries
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_lib_rx #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_sequence_library #(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_lib_rx #(CHANNELS, CHANNEL_WIDTH))
    `uvm_sequence_library_utils(uvm_byte_array_mii::sequence_lib_rx #(CHANNELS, CHANNEL_WIDTH))

    function new(string name = "sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void load_sequences();
        this.add_sequence(uvm_byte_array_mii::sequence_rx_burst #(CHANNELS, CHANNEL_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_mii::sequence_rx_avg #(CHANNELS, CHANNEL_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_mii::sequence_rx_slow #(CHANNELS, CHANNEL_WIDTH)::get_type());
    endfunction

endclass

class sequence_lib_tx #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_sequence_library #(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_lib_tx #(CHANNELS, CHANNEL_WIDTH))
    `uvm_sequence_library_utils(uvm_byte_array_mii::sequence_lib_tx #(CHANNELS, CHANNEL_WIDTH))

    function new(string name = "sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void load_sequences();
        this.add_sequence(uvm_byte_array_mii::sequence_tx_random #(CHANNELS, CHANNEL_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_mii::sequence_tx_alternate #(CHANNELS, CHANNEL_WIDTH)::get_type());
    endfunction

endclass
