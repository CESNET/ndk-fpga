//-- sequence_base.sv: sequence base
//-- Copyright (C) 2025 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


class sequence_base#(
    int unsigned PCIE_TAG_WIDTH,
    int unsigned DMA_PORTS
) extends uvm_sequence;
    `uvm_object_param_utils(uvm_ptc::sequence_base#(PCIE_TAG_WIDTH, DMA_PORTS))
    `uvm_declare_p_sequencer(uvm_ptc::sequencer#(DMA_PORTS));

    protected uvm_reset::sequence_start m_dma_reset;
    protected uvm_reset::sequence_start m_reset;

    protected uvm_common::sequence_library#(uvm_dma::config_sequence, uvm_dma::sequence_item_rq) dma_rq_seq[DMA_PORTS];
    protected uvm_pcie::sequence_comp_lib                                                        pcie_seq_rc;

    logic [DMA_PORTS-1:0] dma_stop;



    function new (string name = "virt_seq");
        super.new(name);
    endfunction


    task body();
        uvm_pcie::config_sequence              pcie_rc_cfg;
        uvm_pcie::pcie_info#(PCIE_TAG_WIDTH)   pcie_rc_info;

        uvm_config_db #(uvm_pcie::pcie_info#(PCIE_TAG_WIDTH))::get(
                p_sequencer.m_pcie_rc,
                "",
                "pcie_info",
                pcie_rc_info
        );

        ///////////////////////////
        // CREATE SEQUENCE
        // RESET
        m_dma_reset = uvm_reset::sequence_start::type_id::create("m_dma_reset", p_sequencer.m_dma_reset);
        m_reset     = uvm_reset::sequence_start::type_id::create("m_reset"    , p_sequencer.m_reset);
        // PCIE
        pcie_seq_rc = uvm_pcie::sequence_comp_lib::type_id::create("pcie_seq_rc", p_sequencer.m_pcie_rc);
        pcie_rc_cfg = new();
        pcie_rc_cfg.payload_size_min = 64;
        pcie_rc_cfg.payload_size_max = 1024;
        pcie_seq_rc.init_sequence(pcie_rc_cfg);
        pcie_seq_rc.min_random_count = 100;
        pcie_seq_rc.max_random_count = 200;

        // DMA
        for(int unsigned it = 0; it <  DMA_PORTS; it++) begin
            dma_rq_seq[it] = uvm_dma::sequence_dma_rq_lib#(DMA_PORTS)::type_id::create(
                                        $sformatf("dma_rq_%0d", it),
                                        p_sequencer.m_dma[it]
                             );
            dma_rq_seq[it].init_sequence();
            dma_rq_seq[it].min_random_count =  50;
            dma_rq_seq[it].max_random_count = 100;
        end

        /////////////////////////////
        //RUN SEQUENCE
        dma_stop = 0;
        fork
            begin
                assert(m_dma_reset.randomize());
                m_dma_reset.start(p_sequencer.m_dma_reset);
            end
            begin
                assert(m_reset.randomize());
                m_reset.start(p_sequencer.m_reset);
            end
        join_none

        #(400ns);

        for(int unsigned it = 0; it <  DMA_PORTS; it++) begin
            fork
                automatic int unsigned index = it;
                begin
                    for (int unsigned jt = 0; jt < 5; jt++) begin
                        assert(dma_rq_seq[index].randomize());
                        dma_rq_seq[index].start(p_sequencer.m_dma[index]);
                    end
                    dma_stop[index] = 1;
                end
            join_none
        end

        fork
            forever begin
                assert(pcie_seq_rc.randomize()) else begin
                    `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize pcie sequence");
                end
                pcie_seq_rc.start(p_sequencer.m_pcie_rc);
            end
        join_none

        // Wait for end
        wait(dma_stop == '1);
    endtask
endclass
