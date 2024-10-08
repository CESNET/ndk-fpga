// test.sv: Virtual sequence
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_logic_vector_array_mfb::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH);
    `uvm_object_param_utils(test::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))
    `uvm_sequence_library_utils(test::sequence_lib_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    function new(string name = "sequence_lib_rx");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(uvm_logic_vector_array_mfb::config_sequence param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
        this.add_sequence(uvm_logic_vector_array_mfb::sequence_full_speed_rx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::get_type());
    endfunction

endclass

class virt_seq#(SECTION_LENGTH, INTERVAL_LENGTH, INTERVAL_COUNT, SHAPING_TYPE, OUTPUT_SPEED, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(test::virt_seq#(SECTION_LENGTH, INTERVAL_LENGTH, INTERVAL_COUNT, SHAPING_TYPE, OUTPUT_SPEED, MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))
    `uvm_declare_p_sequencer(uvm_rate_limiter::virt_sequencer#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH))

    uvm_reset::sequence_start                                                                                      m_reset;
    uvm_mfb::sequence_full_speed_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH) m_mfb_tx_seq;
    uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)                                                          m_mfb_rx_data_seq;
    uvm_logic_vector::sequence_endless#(MFB_META_WIDTH)                                                            m_mfb_rx_meta_seq;
    uvm_rate_limiter::regmodel#(INTERVAL_COUNT)                                                                    m_regmodel;

    // only half of the registers get configured (to test looping from the first register)
    protected rand int interval_speed [INTERVAL_COUNT/2];
    constraint speed_constr { foreach (interval_speed[i])
                                interval_speed[i] inside {[0:OUTPUT_SPEED]};
                            }

    function new(string name = "virt_seq");
        super.new(name);
    endfunction

    function void regmodel_set(uvm_rate_limiter::regmodel#(INTERVAL_COUNT) m_regmodel);
        this.m_regmodel = m_regmodel;
    endfunction

    function void init();
        m_reset           = uvm_reset::sequence_start::type_id::create("rst_seq");
        m_mfb_tx_seq      = uvm_mfb::sequence_full_speed_tx#(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)::type_id::create("m_mfb_tx_seq");
        m_mfb_rx_data_seq = uvm_logic_vector_array::sequence_lib#(MFB_ITEM_WIDTH)::type_id::create("m_mfb_rx_data_seq");
        m_mfb_rx_meta_seq = uvm_logic_vector::sequence_endless#(MFB_META_WIDTH)::type_id::create("m_mfb_rx_meta_seq");
        m_mfb_rx_data_seq.init_sequence();
        void'(this.randomize());
    endfunction;

    task run_reset();
        m_reset.randomize();
        m_reset.start(p_sequencer.m_reset);
    endtask

    task configure();
        uvm_status_e status;
        m_regmodel.status.write(status, 'h02);
        m_regmodel.section.write(status, SECTION_LENGTH);
        m_regmodel.interval.write(status, INTERVAL_LENGTH);
        for (int i = 0; i < INTERVAL_COUNT/2; i++)
            m_regmodel.speed[i].write(status, interval_speed[i]);
        if (SHAPING_TYPE != 0)
            m_regmodel.status.write(status, 'h28);
    endtask

    task run_shaping();
        uvm_status_e status;
        m_regmodel.status.write(status, 'h04);
    endtask

    task run_mfb_tx();
        forever begin
            void'(m_mfb_tx_seq.randomize());
            m_mfb_tx_seq.start(p_sequencer.m_mfb_tx);
        end
    endtask

    task run_mfb_rx_data();
        forever begin
            void'(m_mfb_rx_data_seq.randomize());
            m_mfb_rx_data_seq.start(p_sequencer.m_mfb_rx_data);
        end
    endtask

    task run_mfb_rx_meta();
        forever begin
            void'(m_mfb_rx_meta_seq.randomize());
            m_mfb_rx_meta_seq.start(p_sequencer.m_mfb_rx_meta);
        end
    endtask

    task body();
        fork
            run_reset();
        join_none

        #(200ns);

        fork
            configure();
        join_none

        #(200ns);

        fork
            run_shaping();
        join_none

        fork
            run_mfb_tx();
            run_mfb_rx_data();
            run_mfb_rx_meta();
        join_any
    endtask

endclass
