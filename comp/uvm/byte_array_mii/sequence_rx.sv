/*
 * file       : sequence_rx.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array - MII RX Sequences
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_rx_burst #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_rx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_rx_burst #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_random #(8) random = new;
        super.new(name);

        this.ipg_gen = new("simple_sequence.ipg_gen", CHANNEL_WIDTH, 3*CHANNEL_WIDTH);
        random.ce_gen_config = this.ce_gen_config;
        this.start_msg = "Sequence RX Burst is running!\n";
        $cast(this.ce_gen, random);
    endfunction: new
endclass

class sequence_rx_avg #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_rx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_rx_avg #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_random #(8) random = new;
        super.new(name);

        this.ipg_gen = new("simple_sequence.ipg_gen", 3*CHANNEL_WIDTH, 16*CHANNEL_WIDTH);
        random.ce_gen_config = this.ce_gen_config;
        this.start_msg = "Sequence RX Avg is running!\n";
        $cast(this.ce_gen, random);
    endfunction: new
endclass

class sequence_rx_slow #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_rx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_rx_slow #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_random #(8) random = new;
        super.new(name);

        this.ipg_gen = new("simple_sequence.ipg_gen", 16*CHANNEL_WIDTH, 64*CHANNEL_WIDTH);
        random.ce_gen_config = this.ce_gen_config;
        this.start_msg = "Sequence RX Slow is running!\n";
        $cast(this.ce_gen, random);
    endfunction: new
endclass
