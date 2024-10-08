/*
 * file       : sequence.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array - MII Base class for TX Sequences,
 *              this sequence is used to configure specific sequences
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_tx_base #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_sequence #(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_tx_base #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------
    localparam CHANNEL_BYTES = CHANNEL_WIDTH >> 3;

    // Clock enable generator
    uvm_byte_array_mii::ce_generator_base ce_gen;
    string start_msg = "sequence_tx_base is running";

    // RANDOMIZATION
    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 100;
    int unsigned hl_transactions_max = 1000;

    uvm_byte_array_mii::ce_gen_config ce_gen_config;

    constraint c_hl_transactions{
        hl_transactions inside {[hl_transactions_min : hl_transactions_max]};
        hl_transactions % 2 == 0;
    };

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);

        if (!uvm_config_db #(uvm_byte_array_mii::ce_gen_config)::get(p_sequencer, "", "ce_gen_config", ce_gen_config)) begin
            ce_gen_config = new();
            uvm_config_db #(uvm_byte_array_mii::ce_gen_config)::set(p_sequencer, "", "ce_gen_config", ce_gen_config);
        end
    endfunction: new

    // Generates transactions
    task body;
        INITIALIZED : assert(ce_gen != null);
        `uvm_info(get_name(), start_msg, UVM_DEBUG)

        for (int i = 0; i < hl_transactions; i++) begin
            req = uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH)::type_id::create("req");
            start_item(req);
            req.clk_en = this.ce_gen.get_ce();
            finish_item(req);
        end
    endtask
endclass
