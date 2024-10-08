/*
 * file       : sequence.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array - MII Base class for RX Sequences,
 *              this sequence is used to configure specific sequences
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_rx_base #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_sequence #(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_mii::sequence_rx_base #(CHANNELS, CHANNEL_WIDTH))
    `uvm_declare_p_sequencer(uvm_mii::sequencer #(CHANNELS, CHANNEL_WIDTH))

    // -----------------------
    // Parameters.
    // -----------------------
    localparam CHANNEL_BYTES = CHANNEL_WIDTH >> 3;
    string start_msg;

    // High level transaction
    uvm_byte_array::sequence_item frame;
    // High level sequencer
    uvm_byte_array_mii::sequencer hi_sqr;

    // Wrapper
    uvm_byte_array_mii::wrapper wrapper;
    // Random IPC generator and appender
    uvm_byte_array_mii::ipg_gen ipg_gen;
    // Channel alligner
    uvm_byte_array_mii::channel_align #(CHANNEL_WIDTH) channel_align;
    // Data buffer
    uvm_byte_array_mii::data_buffer #(CHANNELS, CHANNEL_WIDTH) data_buffer;
    // Clock enable generator
    uvm_byte_array_mii::ce_generator_base ce_gen;

    // RANDOMIZATION
    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min = 10;
    int unsigned hl_transactions_max = 200;

    int unsigned attempts = 0;
    const int unsigned MAX_ATTEMPTS = 10000;

    uvm_byte_array_mii::ce_gen_config ce_gen_config;

    constraint c_hl_transactions{
        hl_transactions inside {[hl_transactions_min : hl_transactions_max]};
    };

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);
        wrapper = new("simple_sequence.wrapper");
        channel_align = new("simple_sequence.channel_align");
        data_buffer = new("simple_sequence.data_buffer");

        if (!uvm_config_db #(uvm_byte_array_mii::ce_gen_config)::get(p_sequencer, "", "ce_gen_config", ce_gen_config)) begin
            ce_gen_config = new();
            uvm_config_db #(uvm_byte_array_mii::ce_gen_config)::set(p_sequencer, "", "ce_gen_config", ce_gen_config);
        end
    endfunction: new

    task try_get();
        if (frame == null && hl_transactions != 0) begin
            hi_sqr.byte_array_sequencer.try_next_item(frame);
            attempts++;
            if (frame != null) begin
                hl_transactions--;
                attempts = 0;
            end
        end
    endtask

    // Generates transactions
    task body;
        INITIALIZED : assert(wrapper != null && ipg_gen != null && channel_align != null && data_buffer != null && ce_gen != null);

        if(!uvm_config_db #(uvm_byte_array_mii::sequencer)::get(p_sequencer, "", "hi_sqr", hi_sqr)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end

        `uvm_info(get_name(), start_msg, UVM_DEBUG)

        send_init();
        while (hl_transactions > 0 || frame != null) begin
            try_get();
            if (attempts > MAX_ATTEMPTS) begin
                break;
            end
            if (frame != null) begin
                byte unsigned data[$] = {frame.data};
                logic control[$];
                bit ce;

                // Wraps data and generates control
                this.wrapper.wrap_data(data, control);
                // Generates IPC and appends it to end of transaction
                this.ipg_gen.generate_ipg(data, control);
                // Aligns next start of frame to first byte of next channel
                this.channel_align.align(data, control);
                // Adds data to buffer
                this.data_buffer.add(data, control);

                while (this.data_buffer.get(data, control)) begin
                    req = uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH)::type_id::create("req");
                    ce = this.ce_gen.get_ce();

                    while (ce != 1'b1) begin
                        start_item(req);
                        req.randomize();
                        req.clk_en = ce;
                        finish_item(req);

                        ce = this.ce_gen.get_ce();
                    end

                    start_item(req);
                    for (int i = 0; i < CHANNELS; i++) begin
                        req.data[i] = {>>1{ { <<8{ data[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } } }};
                        req.control[i] = { <<1{ control[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } };
                        req.clk_en = 1;
                    end
                    finish_item(req);

                    data.delete();
                    control.delete();
                end
                frame = null;
                hi_sqr.byte_array_sequencer.item_done();
            end
        end

        if (!this.data_buffer.is_empty()) begin
            byte unsigned data[$];
            logic control[$];
            bit ce;

            ce = this.ce_gen.get_ce();

            while (ce != 1'b1) begin
                start_item(req);
                req.randomize();
                req.clk_en = ce;
                finish_item(req);

                ce = this.ce_gen.get_ce();
            end

            this.data_buffer.flush(data, control);
            req = uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH)::type_id::create("req");
            start_item(req);
            for (int i = 0; i < CHANNELS; i++) begin
                req.data[i] = {>>1{ { <<8{ data[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } } }};
                req.control[i] = { <<1{ control[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } };
                req.clk_en = 1;
            end
            finish_item(req);
        end
    endtask

    task send_init();
        uvm_byte_array_mii::ipg_gen ipg_gen_init = new("simple_sequence.ipg_gen", 16*CHANNEL_WIDTH, 16*CHANNEL_WIDTH);
        byte unsigned data[$];
        logic control[$];
        bit ce;

        ipg_gen_init.generate_ipg(data, control);
        // Aligns next start of frame to first byte of next channel
        this.channel_align.align(data, control);
        // Adds data to buffer
        this.data_buffer.add(data, control);

        while (this.data_buffer.get(data, control)) begin
            req = uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH)::type_id::create("req");
            ce = this.ce_gen.get_ce();

            while (ce != 1'b1) begin
                start_item(req);
                req.randomize();
                req.clk_en = ce;
                finish_item(req);

                ce = this.ce_gen.get_ce();
            end

            start_item(req);
            for (int i = 0; i < CHANNELS; i++) begin
                req.data[i] = {>>1{ { <<8{ data[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } } }};
                req.control[i] = { <<1{ control[i * CHANNEL_BYTES : (i + 1) * CHANNEL_BYTES - 1] } };
                req.clk_en = 1;
            end
            finish_item(req);

            data.delete();
            control.delete();
        end
    endtask
endclass
