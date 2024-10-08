// sequence.sv: AVMM sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// Slave
class sequence_slave_simple #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_sequence #(sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_object_param_utils(uvm_avmm::sequence_slave_simple #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 1000;
    rand int unsigned transaction_count;

    constraint c_transaction_count { transaction_count inside { [transaction_count_min : transaction_count_max] }; }

    // Constructor
    function new(string name = "sequence_slave_simple");
        super.new(name);
    endfunction

    // Generates transactions
    task body;
        req = sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::type_id::create("req");
        repeat (transaction_count) begin
            start_item(req);
            assert(req.randomize() != 0)
            else begin
                `uvm_fatal(m_sequencer.get_full_name(), "sequence_slave_simple cannot randomize!")
            end
            finish_item(req);
        end
    endtask

endclass

// Master
class sequence_master #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_common::sequence_base #(config_sequence, sequence_item_response #(DATA_WIDTH), sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_object_param_utils(uvm_avmm::sequence_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    int unsigned transaction_count_min = 1000;
    int unsigned transaction_count_max = 10000;
    rand int unsigned transaction_count;

    constraint c_transaction_count { transaction_count inside { [transaction_count_min : transaction_count_max] }; }

    // Response input fifo
    protected uvm_tlm_analysis_fifo #(response_item #(DATA_WIDTH)) response_in;

    // Constructor
    function new (string name = "sequence_master");
        super.new(name);
    endfunction

    virtual function void config_set(CONFIG_TYPE cfg);
        super.config_set(cfg);

        transaction_count_min = cfg.transaction_count_min;
        transaction_count_max = cfg.transaction_count_max;
    endfunction

    // Get response fifo from sequence
    task pre_body();
        super.pre_body();

        assert(uvm_config_db #(uvm_tlm_analysis_fifo #(response_item #(DATA_WIDTH)))::get(m_sequencer, "", "response_in", response_in))
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot get response input fifo");
        end
    endtask

    // Generate transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            if (response_in.try_get(response)) begin
                send_response(response);
                current_transaction_count++;
            end
            else begin
                send_empty();
            end
        end
    endtask

    // Send response
    task send_response(response_item #(DATA_WIDTH) response);
        int randomization_result;
        start_item(req);

        randomization_result = req.randomize() with {
            readdatavalid == 1;
            readdata == response.readdata;
        };

        assert(randomization_result != 0)
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("%s cannot randomize!", get_type_name()))
        end
        finish_item(req);
    endtask

    // Send empty response
    task send_empty();
        int randomization_result;
        start_item(req);

        randomization_result = req.randomize() with {
            readdatavalid == 0;
        };

        assert(randomization_result != 0)
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("%s cannot randomize!", get_type_name()))
        end
        finish_item(req);
    endtask

endclass

class sequence_master_endless #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_endless #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Constructor
    function new (string name = "sequence_master_endless");
        super.new(name);
    endfunction

    // Generate transactions
    task body;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        forever begin
            if (response_in.try_get(response)) begin
                send_response(response);
            end
            else begin
                send_empty();
            end
        end
    endtask

endclass

// Always sets the READY signals
class sequence_master_fullspeed #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_fullspeed #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Constructor
    function new(string name = "sequence_master_fullspeed");
        super.new(name);
    endfunction

    // Generate transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            if (response_in.try_get(response)) begin
                send_response(response);
                current_transaction_count++;
            end
            else begin
                send_empty();
            end
        end
    endtask

    task send_response(response_item #(DATA_WIDTH) response);
        int randomization_result;
        start_item(req);

        randomization_result = req.randomize() with {
            ready == 1;
            readdatavalid == 1;
            readdata == response.readdata;
        };

        assert(randomization_result != 0)
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("%s cannot randomize!", get_type_name()))
        end
        finish_item(req);
    endtask

    task send_empty();
        int randomization_result;
        start_item(req);

        randomization_result = req.randomize() with {
            ready == 1;
            readdatavalid == 0;
        };

        assert(randomization_result != 0)
        else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("%s cannot randomize!", get_type_name()))
        end
        finish_item(req);
    endtask

endclass

class sequence_master_static_latency #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_static_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    time latency_min = 50ns;
    time latency_max = 150ns;
    rand time latency;

    constraint c_latency { latency inside { [latency_min : latency_max] }; }

    // Constructor
    function new(string name = "sequence_master_static_latency");
        super.new(name);
    endfunction

    virtual function void config_set(CONFIG_TYPE cfg);
        super.config_set(cfg);

        latency_min = cfg.latency_min;
        latency_max = cfg.latency_max;
    endfunction

    // Generates transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            if (response_in.try_get(response)) begin
                latency_wait(response.timestamp);

                send_response(response);
                current_transaction_count++;
            end
            else begin
                send_empty();
            end
        end
    endtask

    // Latency logic
    task latency_wait(time timestamp);
        time delay = $time - timestamp;
        if (latency > delay) begin
            #(latency - delay);
        end
    endtask

endclass

class sequence_master_dynamic_latency #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master_static_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_dynamic_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Constructor
    function new(string name = "sequence_master_dynamic_latency");
        super.new(name);
    endfunction

    // Generate transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            if (response_in.try_get(response)) begin
                std::randomize(latency) with { latency inside { [latency_min : latency_max] }; }; // Randomize latency
                latency_wait(response.timestamp);

                send_response(response);
                current_transaction_count++;
            end
            else begin
                send_empty();
            end
        end
    endtask

endclass

class sequence_master_dynamic_minmax_latency #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master_static_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_dynamic_minmax_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // Constructor
    function new(string name = "sequence_master_dynamic_minmax_latency");
        super.new(name);
    endfunction

    // Generate transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            if (response_in.try_get(response)) begin
                // Randomize latency
                std::randomize(latency) with { latency dist { latency_min := 50, latency_max := 50 }; }; // 50% min / 50% max
                latency_wait(response.timestamp);

                send_response(response);
                current_transaction_count++;
            end
            else begin
                send_empty();
            end
        end
    endtask

endclass

class sequence_master_bursting #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends sequence_master_static_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH);
    `uvm_object_param_utils(uvm_avmm::sequence_master_bursting #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    // --------- //
    // Variables //
    // --------- //

    int unsigned excited_count_min = 40;
    int unsigned excited_count_max = 100;
    int unsigned excited_counter;
    logic excited_first;

    // Constructor
    function new(string name = "sequence_master_bursting");
        super.new(name);
    endfunction

    virtual function void config_set(CONFIG_TYPE cfg);
        super.config_set(cfg);

        excited_count_min = cfg.excited_count_min;
        excited_count_max = cfg.excited_count_max;
    endfunction

    // Generate transactions
    task body;
        int unsigned current_transaction_count = 0;
        response_item #(DATA_WIDTH) response;

        excited_counter = 0;
        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        while (current_transaction_count < transaction_count) begin
            // Bursting logic
            if (excited_counter == 0) begin
                std::randomize(latency)        with { latency inside { [latency_min : latency_max] }; };
                std::randomize(excited_counter) with { excited_counter inside { [excited_count_min : excited_count_max] }; };
                excited_first = 1;
            end

            if (response_in.used() > excited_counter) begin
                response_in.get(response);

                if (excited_first) begin
                    latency_wait(response.timestamp);
                    excited_first = 0;
                end

                send_response(response);
                current_transaction_count++;
                excited_counter--;
            end
            else begin
                send_empty();
            end
        end
    endtask

endclass

class sequence_library_master #(int unsigned ADDRESS_WIDTH, int unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_common::sequence_library #(config_sequence, sequence_item_response #(DATA_WIDTH), sequence_item_request #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH));
    `uvm_object_param_utils(uvm_avmm::sequence_library_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))
    `uvm_sequence_library_utils(uvm_avmm::sequence_library_master #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    function new(string name = "sequence_library_master");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);

        this.add_sequence(sequence_master                        #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
        this.add_sequence(sequence_master_fullspeed              #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
        this.add_sequence(sequence_master_static_latency         #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
        this.add_sequence(sequence_master_dynamic_latency        #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
        this.add_sequence(sequence_master_dynamic_minmax_latency #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
        this.add_sequence(sequence_master_bursting               #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)::get_type());
    endfunction

endclass
