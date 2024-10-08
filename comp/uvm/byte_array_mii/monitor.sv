/*
 * file       : monitor.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM MII - Byte array monitor
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

`ifndef BYTE_ARRAY_MII_MONITOR_SV
`define BYTE_ARRAY_MII_MONITOR_SV

class monitor #(int unsigned CHANNELS, int unsigned CHANNEL_WIDTH) extends uvm_byte_array::monitor;
    `uvm_component_param_utils(uvm_byte_array_mii::monitor #(CHANNELS, CHANNEL_WIDTH))

    localparam BYTES = CHANNEL_WIDTH >> 3;

    // Used to send transactions to all connected components.
    uvm_analysis_imp #(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH), monitor #(CHANNELS, CHANNEL_WIDTH)) analysis_export;
    uvm_byte_array::sequence_item hl_tr; // high level transaction

    local byte unsigned data[$];

    typedef enum {INIT, IDLE, PREAMBLE, DATA} state_t;
    state_t state;

    local byte unsigned current_byte;
    local logic unsigned current_control;

    // Used to check if start of frame is aligned to first byte of channel
    local int unsigned byte_lane_id;

    local int unsigned counter;
    local int unsigned init_counter = 0;
    local int ipg_size = 0;

    // Creates new instance of this class.
    function new (string name, uvm_component parent);
        super.new(name, parent);

        WHOLE_BYTES : assert((CHANNEL_WIDTH & 7) == 0);
        analysis_export = new("analysis_export", this);
        state = INIT;
    endfunction

    // Instantiates child components.
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    function void fsm();
        case (state)
            INIT:
                begin
                    init_counter++;
                    if (current_control == 1'b1) begin
                        if (current_byte == 8'hFB) begin
                            state = PREAMBLE;
                            counter = 0;
                            init_counter = 0;
                        end else if (current_byte == 8'h07) begin
                            state = IDLE;
                            init_counter = 0;
                            ipg_size = 0;
                        end
                    end
                    if (init_counter > 1024 * 10) begin
                        `uvm_fatal(get_full_name(), "uvm_byte_array_mii::monitor - Failed to initialize MII line!\n")
                    end
                end
            IDLE :
                begin
                    if (current_control == 1'b1) begin
                        if (current_byte == 8'hFB) begin
                            state = PREAMBLE;
                            counter = 0;
                            if (ipg_size < MIN_IPG_SIZE) begin
                                `uvm_error(get_full_name(), $sformatf("uvm_byte_array_mii::monitor - IPG too small, min. required: %0d, actual size: %0d!\n", ipg_size, MIN_IPG_SIZE))
                            end
                            if (byte_lane_id != 0) begin
                                `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Start of frame delimiter not aligned to first byte of channel!\n")
                            end
                            ipg_size = 0;
                        end else if (current_byte == 8'h07) begin
                            state = IDLE;
                            ipg_size++;
                        end else begin
                            this.fsm_print_state();
                            `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Unexpected control character!\n")
                        end
                    end else if (current_control == 1'b0) begin
                        this.fsm_print_state();
                        `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Data started without start of frame delimiter!\n")
                    end else begin
                        this.fsm_print_state();
                        `uvm_fatal(get_full_name(), "uvm_byte_array_mii::monitor - Undefined control signal!\n");
                    end
                end
            PREAMBLE :
                begin
                    if (current_control == 1'b1) begin
                        this.fsm_print_state();
                        `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Unexpected control character!\n")
                    end else if (current_control == 1'b0) begin
                        if (current_byte == 8'h55) begin
                            counter++;
                        end else if (current_byte == 8'hD5) begin
                            if (counter == 6) begin
                                state = DATA;
                            end else begin
                                this.fsm_print_state();
                                `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Preamble too short or too long!\n")
                            end
                        end else begin
                            this.fsm_print_state();
                            `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Invalid preamble!\n")
                        end
                    end else begin
                        this.fsm_print_state();
                        `uvm_fatal(get_full_name(), "uvm_byte_array_mii::monitor - Undefined control signal!\n");
                    end
                end
            DATA :
                begin
                    if (current_control == 1'b1) begin
                        if (current_byte == 8'hFD) begin
                            this.send_data();
                            state = IDLE;
                        end else if (current_byte == 8'hFE) begin
                            state = DATA;
                            this.data.push_back(current_byte);
                        end else begin
                            this.fsm_print_state();
                            `uvm_error(get_full_name(), "uvm_byte_array_mii::monitor - Unexpected control character!\n");
                        end
                    end else if (current_control == 1'b0) begin
                        this.data.push_back(current_byte);
                        state = DATA;
                    end else begin
                        this.fsm_print_state();
                        `uvm_fatal(get_full_name(), "uvm_byte_array_mii::monitor - Undefined control signal!\n");
                    end
                end
        endcase
    endfunction

    function void fsm_print_state();
        `uvm_info(get_full_name(), $sformatf("uvm_byte_array_mii::monitor - FSM state: %s\n", state.name()), UVM_NONE)
    endfunction

    function void send_data();
        hl_tr = uvm_byte_array::sequence_item::type_id::create("hl_tr");
        hl_tr.data = new[this.data.size()];
        hl_tr.data = this.data;
        analysis_port.write(hl_tr);
    endfunction

    virtual function void write(uvm_mii::sequence_item #(CHANNELS, CHANNEL_WIDTH) tr);
        byte unsigned channel_data[] = {<<8{{<<CHANNEL_WIDTH{tr.data}}}};
        logic channel_control[] = {<<1{{<<BYTES{tr.control}}}};

        if (tr.clk_en != 1) begin
            return;
        end

        for (int i = 0; i < CHANNELS * BYTES; i++) begin
            current_byte = channel_data[i];
            current_control = channel_control[i];
            byte_lane_id = i % BYTES;
            this.fsm();
        end
    endfunction

endclass

`endif
