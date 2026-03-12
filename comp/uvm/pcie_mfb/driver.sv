// driver.sv: pcie driver
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class driver#(
    direction_t  DIR,
    meta_position_t META_TYPE,
    device_t DEVICE
) extends uvm_pcie::driver;
    `ndk_component_param_utils(
        uvm_pcie_mfb::driver#(DIR, META_TYPE, DEVICE),
        $sformatf("uvm_pcie_mfb::driver#(%s,%s,%s)",DIR, META_TYPE, DEVICE)
    );

    uvm_common::fifo#(uvm_logic_vector_array::sequence_item #(32))            data_fifo;
    uvm_common::fifo#(uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))) meta_fifo;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        data_fifo = new("data_fifo", this);
        meta_fifo = new("meta_fifo", this);
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= super.used();
        ret |= data_fifo.used();
        ret |= meta_fifo.used();
        return ret;
    endfunction

    task run_phase(uvm_phase phase);
        uvm_logic_vector_array::sequence_item #(32)            data;
        uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE)) meta;

        forever begin
            wait(data_fifo.size() < 8 || meta_fifo.size() < 8);
            seq_item_port.get_next_item(req);

            data = uvm_logic_vector_array::sequence_item #(32)           ::type_id::create("mfb_fifo", this);
            meta = uvm_logic_vector::sequence_item #(meta_width_get(DIR, DEVICE))::type_id::create("mfb_fifo", this);

            if (DEVICE == DEV_XILINX) begin
                if (DIR ==  MFB_CC) begin
                    logic [32-1:0] hdr_data[3];
                    uvm_pcie::completer_header hdr_cast;

                    assert($cast(hdr_cast, req)) else `uvm_fatal(this.get_full_name(), $sformatf("NOT COMPLEATER HEADER %s", req.convert2string()));

                    uvm_pcie_axi::hdr_cc_set(hdr_data, hdr_cast);
                    data.data = {hdr_data, req.data};
                    meta.data = 'x;
                end else if (DIR == MFB_RQ) begin
                    logic [32-1:0] hdr_data[4];
                    logic [8-1:0] target_fce = 0;
                    uvm_pcie::request_header hdr_cast;

                    assert($cast(hdr_cast, req)) else `uvm_fatal(this.get_full_name(), $sformatf("NOT COMPLEATER HEADER %s", req.convert2string()));

                    uvm_pcie_axi::hdr_rq_set(hdr_data, hdr_cast);
                    data.data = {hdr_data, req.data};
                    meta.data = 'x;
                    meta.data[163:160] = hdr_cast.fbe;
                    meta.data[167:164] = hdr_cast.lbe;
                end else begin
                    `uvm_fatal(this.get_full_name(), "\n\tTHIS IS NOT IMPLEMENTED\n");
                end
            end else if (DEVICE == DEV_INTEL) begin
                logic [128-1:0] hdr;
                logic [32-1:0]  prefix;
                logic [3-1:0]   bar;
                logic [1-1:0]   error;

                uvm_pcie_avst::hdr_set(req, hdr, prefix, error, bar, data.data, /*cfg.bar*/);
                //Change DWORD ORDER - more info P-TILE intel
                hdr = { <<32 {hdr}};

                if (DIR ==  MFB_CC) begin
                    meta.data = 'x;
                    meta.data[128-1:0] = {prefix, hdr[96-1:0]};
                end else if (DIR ==  MFB_RQ) begin
                    meta.data = 'x;
                    meta.data[160-1:0] = {prefix, hdr};
                end else if (DIR ==  MFB_RC) begin
                    meta.data = 'x;
                    meta.data[128-1:0] = {prefix, hdr[96-1:0]};
                end else begin
                    `uvm_fatal(this.get_full_name(), "\n\tTHIS IS NOT IMPLEMENTED\n");
                end
            end else begin
                `uvm_fatal(this.get_full_name(), "\n\tUNSUPPORTED DEVICE\n");
            end

            data_fifo.push_back(data);
            meta_fifo.push_back(meta);
            seq_item_port.item_done();
        end
    endtask

endclass


