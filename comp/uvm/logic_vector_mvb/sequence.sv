//-- sequence.sv: Mvb sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class sequence_simple_rx_base #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_base #(config_sequence, uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_simple_rx_base #(ITEMS, ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_mvb::sequencer #(ITEMS, ITEM_WIDTH))

    uvm_logic_vector::sequencer #(ITEM_WIDTH)     hi_sqr;
    uvm_logic_vector::sequence_item #(ITEM_WIDTH) frame;
    uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)   gen;
    string name;

    typedef enum {state_last, state_next} state_t;
    local state_t state;

    //////////////////////////////////
    // RANDOMIZATION
    rand int unsigned hl_transactions;
    int unsigned hl_transactions_min =  20;
    int unsigned hl_transactions_max = 300;

    constraint c_hl_transactions{
        hl_transactions inside {[hl_transactions_min:hl_transactions_max]};
    };

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_rx_base");
        super.new(name);
        this.name = name;
    endfunction


    // Generates transactions
    task body;
        // Create a request for sequence item
        if(!uvm_config_db #(uvm_logic_vector::sequencer #(ITEM_WIDTH))::get(p_sequencer, "", "hi_sqr", hi_sqr)) begin
            `uvm_fatal(get_type_name(), "Unable to get configuration object")
        end
        `uvm_info(get_full_name(), $sformatf("%s is running", name), UVM_DEBUG)
        req = uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("req");
        gen = uvm_mvb::sequence_item #(ITEMS, ITEM_WIDTH)::type_id::create("gen");
        send_empty();
        req.src_rdy = 0;
        gen.src_rdy = 0;
        state = state_next;
        while (hl_transactions > 0 || state == state_last || gen.src_rdy == 1'b1) begin
            send();
        end
        //Get last response
        get_response(rsp);
    endtask

    // Method which define how the transaction will look.
    task send();

        if (p_sequencer.reset_sync.has_been_reset()) begin
            //SETUP RESET
            assert(gen.randomize() with {src_rdy == 0;});
            state = state_next;
            get_response(rsp);
        end else begin
            if (state == state_next) begin
                create_sequence_item();
            end

            //GET response
            get_response(rsp);

            if (req.src_rdy == 1'b1 && rsp.dst_rdy == 1'b0) begin
                state = state_last;
            end else begin
                state = state_next;
            end
        end

        start_item(req);
        if (state != state_last) begin
            req.copy(gen);
        end
        finish_item(req);
    endtask

    virtual task send_empty();
        start_item(req);
        void'(req.randomize() with {src_rdy == '0;});
        finish_item(req);
    endtask

    // Method which define how the transaction will look.
    virtual task create_sequence_item();
    endtask

endclass

class sequence_rand_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_rand_rx #(ITEMS, ITEM_WIDTH))

    // coeficient is used because we want to use more random distributors
    // uvm_common::rand_length use constant size instead relative ranges
    const int unsigned coeficient = 1024;
    uvm_common::rand_length   rdy;
    int unsigned space = 0;

    // Constructor - creates new instance of this class
    function new(string name = "sequence_rand_rx");
        super.new(name);
        rdy = uvm_common::rand_length_rand::new();
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");

        gen.vld     = 0;
        gen.src_rdy = 1'b0;

        for (int i = 0; i < ITEMS; i++) begin
            if (hl_transactions != 0) begin
                if (space == 0) begin
                    hi_sqr.try_next_item(frame);
                    if (frame != null) begin
                        gen.src_rdy = 1'b1;
                        gen.vld[i]  = 1'b1;
                        gen.data[i] = frame.data;
                        hi_sqr.item_done();
                        frame = null;
                        hl_transactions--;

                        assert(rdy.randomize());
                        space = rdy.m_value/coeficient;
                    end
                end else begin
                    space--;
                end
            end
        end
    endtask

    virtual function void config_set(config_sequence cfg);
        this.cfg = cfg;
        rdy.bound_set(cfg.space_size_min*coeficient, cfg.space_size_max*coeficient);
    endfunction
endclass


class sequence_burst_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_burst_rx #(ITEMS, ITEM_WIDTH))

    uvm_common::rand_length   rand_burst_length;
    uvm_common::rand_length   rand_space_length;
    int unsigned burst_length;
    typedef enum {MODE_BURST, MODE_SPACE} mode_t;
    mode_t       burst_mode;

    int unsigned space;

    // modified length of burst.
    rand int unsigned burst_percentage;
    rand int unsigned burst_length_min;
    rand int unsigned burst_length_max;

    constraint c_probability {
        burst_length_min inside {[10:100]};
        burst_length_max inside {[10:100]};
        burst_length_min <= burst_length_max;

        burst_percentage dist {[0:29] :/ 10, [30:49] :/ 20, [50:79] :/ 40, [80:100] :/ 30};
    }


    // Constructor - creates new instance of this class
    function new(string name = "sequence_burst_rx");
        super.new(name);
        rand_burst_length = uvm_common::rand_length_rand::new();
        rand_space_length = uvm_common::rand_length_rand::new();
        burst_length = 0;
        space        = 0;
        //first in body is decision so the first mode will be MODE_SPACE
        burst_mode         = MODE_BURST;
   endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");

        gen.vld     = 0;
        gen.src_rdy = 1'b0;

        if (burst_length == 0) begin
            case (burst_mode)
                MODE_SPACE : begin
                    assert(rand_burst_length.randomize());
                    burst_length = rand_burst_length.m_value;
                    burst_mode   = MODE_BURST;
                end

                MODE_BURST : begin
                    assert(rand_space_length.randomize());
                    burst_length = rand_space_length.m_value;
                    burst_mode   = MODE_SPACE;
                end
            endcase
        end else begin
            burst_length--;
        end

        if (burst_mode == MODE_BURST) begin
            for (int i = 0; i < ITEMS; i++) begin
                if (hl_transactions != 0) begin
                    if (space == 0) begin
                        hi_sqr.try_next_item(frame);
                        if (frame != null) begin
                            gen.src_rdy = 1'b1;
                            gen.vld[i]  = 1'b1;
                            gen.data[i] = frame.data;
                            hi_sqr.item_done();
                            frame = null;
                            hl_transactions--;

                            space = cfg.space_size_min;
                        end
                    end else begin
                        space--;
                    end
                end
            end
        end
    endtask

    task body();
        const real burst_min = real'(burst_length_min*(cfg.space_size_min + 1))/100;
        const real burst_max = real'(burst_length_max*(cfg.space_size_min + 1))/100;

        //BURST SIZE
        rand_burst_length.bound_set(burst_min*burst_percentage, burst_max*burst_percentage);
        rand_space_length.bound_set(burst_min*(100 - burst_percentage), burst_max*(100 - burst_percentage));

        super.body();
    endtask
endclass


class sequence_full_speed_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);

    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_full_speed_rx #(ITEMS, ITEM_WIDTH))

    int unsigned space = 0;
    // Constructor - creates new instance of this class
    function new(string name = "sequence_full_speed_rx");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");
        gen.vld     = 0;
        gen.src_rdy = 1'b0;

        for (int i = 0; i < ITEMS; i++) begin
            if (hl_transactions != 0) begin
                if (space == 0) begin
                    hi_sqr.try_next_item(frame);
                    if (frame != null) begin
                        gen.src_rdy = 1'b1;
                        gen.vld[i]  = 1'b1;
                        gen.data[i] = frame.data;
                        hi_sqr.item_done();
                        hl_transactions--;
                        space = cfg.space_size_min;
                    end
                end else begin
                    space--;
                end
            end
        end
    endtask

    virtual function void config_set(config_sequence cfg);
        this.cfg = cfg;
        space = cfg.space_size_min;
    endfunction
endclass


class sequence_stop_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);

    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_stop_rx #(ITEMS, ITEM_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_stop_rx");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize() with {src_rdy == 0;}) `uvm_fatal(this.get_full_name(), "\n\tfailed to radnomize");
        if (hl_transactions != 0) begin
            hl_transactions--;
        end
    endtask


    virtual function void config_set(config_sequence cfg);
        this.cfg = cfg;
        hl_transactions_min = (cfg.space_size_min + 100) > cfg.space_size_max ? cfg.space_size_min : (cfg.space_size_max - 100);
        hl_transactions_max = cfg.space_size_max;
    endfunction
endclass


class sequence_const_space_rx #(ITEMS, ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_const_space_rx #(ITEMS, ITEM_WIDTH))

    rand int unsigned space_size = 10;
    int unsigned  space_size_min = 0;
    int unsigned  space_size_max = 30;

    int unsigned space = 0;
    // Constructor - creates new instance of this class

    constraint c_space_size{
        space_size dist {[space_size_min:(space_size_min + (space_size_max - space_size_min)/10)]                                              :/ 40,
                         [(space_size_min + (space_size_max - space_size_min)/10):(space_size_min + (space_size_max - space_size_min)/10*2)]   :/ 30,
                         [(space_size_min + (space_size_max - space_size_min)/10*2):(space_size_max - (space_size_max - space_size_min)/10*2)] :/ 20,
                         [(space_size_max - (space_size_max - space_size_min)/10*2):(space_size_max - (space_size_max - space_size_min)/10)]   :/ 5,
                         [(space_size_max - (space_size_max - space_size_min)/10):space_size_max]                                              :/ 5
                     };
    };

    function new(string name = "sequence_full_speed_rx");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");
        gen.vld     = 0;
        gen.src_rdy = 1'b0;

        for (int i = 0; i < ITEMS; i++) begin
            if (hl_transactions != 0) begin
                if (space == 0) begin
                    hi_sqr.try_next_item(frame);
                    if (frame != null) begin
                        gen.src_rdy = 1'b1;
                        gen.vld[i]  = 1'b1;
                        gen.data[i] = frame.data;
                        hi_sqr.item_done();
                        hl_transactions--;
                        space = space_size;
                    end
                end else begin
                    space--;
                end
            end
        end
    endtask

    virtual function void config_set(config_sequence cfg);
        this.cfg = cfg;
        space_size_min = cfg.space_size_min;
        space_size_max = cfg.space_size_max;
    endfunction
endclass


class sequence_const_possition_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_const_possition_rx #(ITEMS, ITEM_WIDTH))

    rand logic [ITEMS-1:0] pos_valid = 1'b1;
    int unsigned space = 0;
    // Constructor - creates new instance of this class

    constraint c_pos_valid{
        $countones(pos_valid) >= 1;
    };

    function new(string name = "sequence_full_speed_rx");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");
        gen.vld     = 0;
        gen.src_rdy = 1'b0;

        for (int i = 0; i < ITEMS; i++) begin
            if (hl_transactions != 0) begin
                if (space == 0) begin
                    if (pos_valid[i]) begin
                        hi_sqr.try_next_item(frame);
                        if (frame != null) begin
                            gen.src_rdy = 1'b1;
                            gen.vld[i]  = 1'b1;
                            gen.data[i] = frame.data;
                            hi_sqr.item_done();
                            hl_transactions--;
                            space = cfg.space_size_min;
                        end
                    end
                end else begin
                    space--;
                end
            end
        end
    endtask

    virtual function void config_set(config_sequence cfg);
        this.cfg = cfg;
    endfunction
endclass

//////////////////////////////////////
// TX LIBRARY
class sequence_lib_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends uvm_common::sequence_library#(config_sequence, uvm_mvb::sequence_item#(ITEMS, ITEM_WIDTH));
  `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_lib_rx#(ITEMS, ITEM_WIDTH))
  `uvm_sequence_library_utils(uvm_logic_vector_mvb::sequence_lib_rx#(ITEMS, ITEM_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        super.init_sequence(param_cfg);
        this.add_sequence(sequence_burst_rx #(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_rand_rx #(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_full_speed_rx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_stop_rx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_const_space_rx#(ITEMS, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_const_possition_rx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
endclass

// Used for full speed tests
class sequence_lib_speed_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_lib_rx#(ITEMS, ITEM_WIDTH);
    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_lib_speed_rx#(ITEMS, ITEM_WIDTH))
    `uvm_sequence_library_utils(uvm_logic_vector_mvb::sequence_lib_speed_rx#(ITEMS, ITEM_WIDTH))

    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(sequence_full_speed_rx#(ITEMS, ITEM_WIDTH)::get_type());
    endfunction
  endclass

//////////////////////////////////////
// PLS DONT PUT IT INTO SEQUENCE LIBRARY.
class sequence_simple_rx #(int unsigned ITEMS, int unsigned ITEM_WIDTH) extends sequence_simple_rx_base #(ITEMS, ITEM_WIDTH);

    `uvm_object_param_utils(uvm_logic_vector_mvb::sequence_simple_rx #(ITEMS, ITEM_WIDTH))

    // Constructor - creates new instance of this class
    function new(string name = "sequence_simple_rx");
        super.new(name);
    endfunction

    virtual task create_sequence_item();
        if (!gen.randomize()) `uvm_fatal(this.get_full_name(), "failed to radnomize");

        //return if src_rdy is zero
        if (gen.src_rdy == 1'b0) begin
            return;
        end

        // generate valid data if src_rdy is set to 1
        for (int i = 0; i < ITEMS; i++) begin
            if (gen.vld[i] == 1'b1 && hl_transactions != 0) begin
                hi_sqr.try_next_item(frame);
                if (frame != null) begin
                    gen.data[i] = frame.data;
                    hi_sqr.item_done();
                    frame = null;
                    hl_transactions--;
                end else begin
                    gen.vld[i] = 1'b0;
                end
            end else begin
                gen.vld[i] = 1'b0;
            end
        end

        if (gen.vld == '0) begin
            gen.src_rdy = 1'b0;
        end
    endtask
endclass

