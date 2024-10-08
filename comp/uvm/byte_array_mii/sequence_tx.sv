/*
 * file       : sequence_tx.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array - MII TX Sequences
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_tx_random #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_tx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_tx_random #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_random #(8) random = new;
        super.new(name);

        this.start_msg = "Sequence TX Random is running!\n";
        random.ce_gen_config = this.ce_gen_config;
        $cast(this.ce_gen, random);
    endfunction: new
endclass

class sequence_tx_alternate #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_tx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_tx_alternate #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_alternate ce_gen = new;
        super.new(name);

        this.start_msg = "Sequence TX Alternate is running!\n";
        $cast(this.ce_gen, ce_gen);
    endfunction: new
endclass

class sequence_tx_one #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array_mii::sequence_tx_base #(CHANNELS, CHANNEL_WIDTH);
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_tx_one #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        uvm_byte_array_mii::ce_generator_one ce_gen = new;
        super.new(name);

        this.start_msg = "Sequence TX One is running!\n";
        $cast(this.ce_gen, ce_gen);
    endfunction: new
endclass
