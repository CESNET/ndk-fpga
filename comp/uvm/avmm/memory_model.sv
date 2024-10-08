// memory_model.sv: Memory model
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class memory_model #(longint unsigned ADDRESS_WIDTH, longint unsigned DATA_WIDTH, int unsigned BURST_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_avmm::memory_model #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH))

    localparam DATA_WIDTH_BYTES = DATA_WIDTH / 8;

    // Model input
    uvm_tlm_analysis_fifo #(request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH)) request_in;

    // Model output
    uvm_analysis_port #(response_item #(DATA_WIDTH)) response_out;

    // ---------- //
    // Parameters //
    // ---------- //

    config_item m_config;
    string memory_filepath = { this.get_full_name(), ".mem" };

    // --------- //
    // Variables //
    // --------- //

    protected int memory_file;

    request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) current_request;

    function new(string name = "memory_model", uvm_component parent = null);
        super.new(name, parent);

        request_in   = new("request_in",   this);
        response_out = new("response_out", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Get configuration object
        assert(uvm_config_db #(config_item)::get(this, "", "m_config", m_config))
        else begin
            `uvm_fatal(this.get_full_name(), "Unable to get configuration object")
        end
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        initialize_memory();
    endfunction

    function void initialize_memory();
        string ferror_message;

        // Memory filepath overwriting
        if (m_config.memory_filepath != "") begin
            memory_filepath = m_config.memory_filepath;
        end

        // Memory file generation
        if (m_config.generated_memory_file) begin
            string command;
            string dev_source;
            case (m_config.generated_memory_file_type)
                config_item::NULL:
                    dev_source = "null";
                config_item::RANDOM:
                    dev_source = "urandom";
                default:
                    dev_source = "urandom";
            endcase

            command = $sformatf("dd if=/dev/%s of=\"%s\" bs=%0d count=1",
                        dev_source,
                        memory_filepath,
                        (2**ADDRESS_WIDTH)*DATA_WIDTH
            );

            assert($system(command) == 0)
            else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\t Cannot run command \"%s\"", command))
            end
        end
        else begin
            memory_filepath = m_config.memory_filepath;
        end

        // Open memory file
        memory_file = $fopen(memory_filepath, "r+b");
        assert($ferror(memory_file, ferror_message) == 0)
        else begin
            `uvm_fatal(this.get_full_name(), $sformatf("\n\t Cannot open an memory file \"%s\"", ferror_message))
        end
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            request_in.get(current_request);

            if (current_request.request_type == READ) begin
                run_read_state();
            end
            else if (current_request.request_type == WRITE) begin
                run_write_state();
            end
        end
    endtask

    task run_read_state();
        response_item #(DATA_WIDTH) item;

        while (current_request.burstcount > 0) begin
            item = response_item #(DATA_WIDTH)::type_id::create("item");
            item.readdata = read_from_memory(current_request.address); // Get data from memory
            item.timestamp = $time;
            response_out.write(item);

            // Update the state properties
            current_request.address++;
            current_request.burstcount--;
        end
    endtask

    task run_write_state();
        request_item #(ADDRESS_WIDTH, DATA_WIDTH, BURST_WIDTH) write_request;

        while (current_request.burstcount > 0) begin
            write_to_memory(current_request.address, current_request.writedata); // Write data to memory

            // Update the state properties
            current_request.address++;
            current_request.burstcount--;

            // Burst writing implementation
            if (current_request.burstcount != 0) begin // Still processing
                request_in.get(write_request);

                // Protocol check
                assert(write_request.request_type != READ)
                else begin
                    `uvm_error(this.get_full_name(), "AVMM Interface: A READ request cannot be sent while burst WRITE request is being processed.")
                end

                // Update the state properties
                current_request.writedata = write_request.writedata;
            end
        end
    endtask

    `define SEEK_SET (0) // Beginning of a file

    function logic [DATA_WIDTH-1 : 0] read_from_memory(logic [ADDRESS_WIDTH-1 : 0] address);
        logic [DATA_WIDTH-1 : 0] data;
        void'($fseek(memory_file, address * DATA_WIDTH_BYTES, `SEEK_SET));
        void'($fread(data, memory_file));
        return data;
    endfunction

    function void write_to_memory(logic [ADDRESS_WIDTH-1 : 0] address, logic [DATA_WIDTH-1 : 0] data);
        for (int i = 0; i < DATA_WIDTH_BYTES; i++) begin
            void'($fseek(memory_file, (address * DATA_WIDTH_BYTES) + (DATA_WIDTH_BYTES-1 - i), `SEEK_SET));
            void'($fwrite(memory_file, "%c", data[8*i +: 8]));
        end
    endfunction

    function void final_phase(uvm_phase phase);
        string command;
        super.final_phase(phase);
        $fclose(memory_file);

        // Delete memory file if generated
        if (m_config.generated_memory_file) begin
            command = $sformatf("rm \"%s\"", memory_filepath);
            assert($system(command) == 0)
            else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\t Cannot run command \"%s\"", command))
            end
        end
    endfunction

endclass
