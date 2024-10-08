/*
 * file       :  sequence_library.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: Iproved sequence library
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_library #(type CONFIG_TYPE, type REQ=uvm_common::sequence_item, type RSP=REQ) extends uvm_sequence_library#(REQ, RSP);
    `uvm_object_param_utils(uvm_common::sequence_library#(CONFIG_TYPE, REQ, RSP))
    //`uvm_sequence_library_utils(uvm_byte_array::sequence_lib)

    CONFIG_TYPE cfg;

    function new(string name = "sequence_library");
        super.new(name);
        cfg = null;
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(CONFIG_TYPE param_cfg = null);
        if (param_cfg == null) begin
            this.cfg = new();
        end else begin
            this.cfg = param_cfg;
        end
    endfunction

    task body();
        uvm_common::sequence_cfg state;
        uvm_object_wrapper wrap;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        if (sequences.size() == 0) begin
            `uvm_error(m_sequencer.get_full_name(), "Sequence library does not contain any sequences. Did you forget to call init_sequence_library() in the constructor?");
            return;
        end

        `uvm_info(m_sequencer.get_full_name(), $sformatf("\nStarting sequence library %s with configuration %s",  get_type_name(), cfg.convert2string()), UVM_DEBUG);
        sequences_executed = 0;

        while (sequences_executed < sequence_count && (state == null || !state.stopped())) begin
            int unsigned select_sequence = $urandom_range(sequences.size()-1);

            execute(sequences[select_sequence]);
            sequences_executed++;
        end

      `uvm_info(m_sequencer.get_full_name(), $sformatf("\n\tEnding sequence library in phase\n%p", seqs_distrib), UVM_DEBUG);
    endtask


    // execute
    // -------
    task execute(uvm_object_wrapper wrap);
        sequence_base#(CONFIG_TYPE, REQ, RSP) cast_sequence;
        string m_sequencer_path;

        uvm_object obj;
        uvm_coreservice_t cs = uvm_coreservice_t::get();
        uvm_factory factory=cs.get_factory();

        m_sequencer_path = (m_sequencer != null) ? m_sequencer.get_full_name() : "";
        obj = factory.create_object_by_type(wrap, m_sequencer_path, $sformatf("%s:%0d", wrap.get_type_name(), seqs_distrib[wrap.get_type_name()]));

        if (!$cast(cast_sequence, obj)) begin
            `uvm_error(m_sequencer.get_full_name(), $sformatf("\n\tCannot convert %s to sequence", obj.get_type_name()));
            return;
        end

        cast_sequence.config_set(cfg);
        `uvm_info(m_sequencer.get_full_name(), {"\n\tExecuting sequence ", cast_sequence.get_type_name()}, UVM_DEBUG);

        if(!cast_sequence.randomize()) begin
            `uvm_error(m_sequencer.get_full_name(), $sformatf("\n\tCannot randomize sequence %s", obj.get_type_name()));
            return;
        end
        cast_sequence.start(m_sequencer, this);
        seqs_distrib[cast_sequence.get_type_name()] = seqs_distrib[cast_sequence.get_type_name()]+1;
    endtask

endclass
