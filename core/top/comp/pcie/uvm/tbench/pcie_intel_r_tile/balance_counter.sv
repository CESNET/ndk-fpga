// balance_counter.sv: Counter of AVST credits
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class balance_counter extends uvm_component;
    `uvm_component_utils(uvm_pcie_intel_r_tile::balance_counter)

    // Input fifos
    uvm_tlm_analysis_fifo #(uvm_avst_crdt::sequence_item #(2)) avst_crdt_hdr_in [3];
    uvm_tlm_analysis_fifo #(uvm_avst_crdt::sequence_item #(4)) avst_crdt_data_in[3];

    // --------- //
    // Variables //
    // --------- //

    credit_counter hp;
    credit_counter hnp;
    credit_counter hcpl;
    credit_counter dp;
    credit_counter dnp;
    credit_counter dcpl;

    // Constructor
    function new(string name = "balance_counter", uvm_component parent = null);
        super.new(name, parent);

        for (int unsigned i = 0; i < 3; i++) begin
            avst_crdt_hdr_in [i] = new($sformatf("avst_crdt_hdr_in_%0d", i), this);
            avst_crdt_data_in[i] = new($sformatf("avst_crdt_data_in_%0d", i), this);
        end
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Header
        hp   = credit_counter::type_id::create("hp"  , this);
        hnp  = credit_counter::type_id::create("hnp" , this);
        hcpl = credit_counter::type_id::create("hcpl", this);
        // Data
        dp   = credit_counter::type_id::create("dp"  , this);
        dnp  = credit_counter::type_id::create("dnp" , this);
        dcpl = credit_counter::type_id::create("dcpl", this);
    endfunction

    task run_phase(uvm_phase phase);
        credit_item temp_credit_item;

        forever begin
            // HP
            get_credit_hdr_item(0, temp_credit_item);
            hp.write(temp_credit_item);
            // HNP
            get_credit_hdr_item(1, temp_credit_item);
            hnp.write(temp_credit_item);
            // HCPL
            get_credit_hdr_item(2, temp_credit_item);
            hcpl.write(temp_credit_item);
            // DP
            get_credit_data_item(0, temp_credit_item);
            dp.write(temp_credit_item);
            // DNP
            get_credit_data_item(1, temp_credit_item);
            dnp.write(temp_credit_item);
            // DCPL
            get_credit_data_item(2, temp_credit_item);
            dcpl.write(temp_credit_item);
        end
    endtask

    protected task get_credit_hdr_item(input int unsigned index, output credit_item credit_item_out);
        uvm_avst_crdt::sequence_item #(2) avst_crdt_hdr_item;
        avst_crdt_hdr_in[index].get(avst_crdt_hdr_item);

        credit_item_out = credit_item::type_id::create("credit_item");
        credit_item_out.init       = avst_crdt_hdr_item.init;
        credit_item_out.init_ack   = avst_crdt_hdr_item.init_ack;
        credit_item_out.update     = avst_crdt_hdr_item.update;
        credit_item_out.update_cnt = avst_crdt_hdr_item.update_cnt;
    endtask

    protected task get_credit_data_item(input int unsigned index, output credit_item credit_item_out);
        uvm_avst_crdt::sequence_item #(4) avst_crdt_data_item;
        avst_crdt_data_in[index].get(avst_crdt_data_item);

        credit_item_out = credit_item::type_id::create("credit_item");
        credit_item_out.init       = avst_crdt_data_item.init;
        credit_item_out.init_ack   = avst_crdt_data_item.init_ack;
        credit_item_out.update     = avst_crdt_data_item.update;
        credit_item_out.update_cnt = avst_crdt_data_item.update_cnt;
    endtask

    function logic is_init_done();
        return (
            hp  .is_init_done() &&
            hnp .is_init_done() &&
            hcpl.is_init_done() &&
            dp  .is_init_done() &&
            dnp .is_init_done() &&
            dcpl.is_init_done()
        );
    endfunction

    task wait_for_init_done();
        hp  .wait_for_init_done();
        hnp .wait_for_init_done();
        hcpl.wait_for_init_done();
        dp  .wait_for_init_done();
        dnp .wait_for_init_done();
        dcpl.wait_for_init_done();
    endtask

    task reduce_balance(balance_item cost);
        hp  .reduce(cost.header.p  );
        hnp .reduce(cost.header.np );
        hcpl.reduce(cost.header.cpl);
        dp  .reduce(cost.data  .p  );
        dnp .reduce(cost.data  .np );
        dcpl.reduce(cost.data  .cpl);
    endtask

    function logic try_reduce_balance(balance_item cost);
        logic is_enough = (
            hp  .is_enough(cost.header.p  ) &&
            hnp .is_enough(cost.header.np ) &&
            hcpl.is_enough(cost.header.cpl) &&
            dp  .is_enough(cost.data  .p  ) &&
            dnp .is_enough(cost.data  .np ) &&
            dcpl.is_enough(cost.data  .cpl)
        );

        if (!is_enough) begin
            return 0;
        end

        assert(hp  .try_reduce(cost.header.p  ));
        assert(hnp .try_reduce(cost.header.np ));
        assert(hcpl.try_reduce(cost.header.cpl));
        assert(dp  .try_reduce(cost.data  .p  ));
        assert(dnp .try_reduce(cost.data  .np ));
        assert(dcpl.try_reduce(cost.data  .cpl));

        return 1;
    endfunction

endclass
