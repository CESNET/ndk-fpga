// sequence_dma_rq.sv : sequence generating dma request.
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause
class config_sequence extends uvm_object;
    //NULL CLASS
    //

    virtual function string covnert2string();
        return "\nNULL CONFIGURATION";
    endfunction
endclass

class sequence_dma_rq#(
    int unsigned DMA_PORTS
) extends uvm_common::sequence_base#(config_sequence, uvm_dma::sequence_item_rq);
    `uvm_object_param_utils(uvm_dma::sequence_dma_rq#(DMA_PORTS))

    localparam PCIE_MAX_REQUEST_SIZE = 128;
    localparam PCIE_MAX_PAYLOAD_SIZE = 64;

    rand logic [sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1:0] unit_id_new[];

    rand int unsigned transactions;
    rand int unsigned max_request_size;
    rand int unsigned max_payload_size;

    rand int unsigned type_ide_write;
    rand int unsigned type_ide_read;

    constraint c_type_ide {
        type_ide_write + type_ide_read == 100;
        type_ide_write inside {[0:100]};
        type_ide_read  inside {[0:100]};
    }

    uvm_dma::seq_info info;

    constraint trans_const {
        transactions dist {
            [1:20]    :/ 5,
            [20:50]   :/ 50,
            [50:100]  :/ 15,
            [100:200] :/ 10,
            [200:500] :/ 5
        };

        unit_id_new.size() dist {
                [1:5] :/ 20,
                [5:15] :/ 10,
                [15:50] :/ 5,
                [50:100] :/ 2,
                [100:300] :/ 1
        };

        if (DMA_PORTS > 1) {
            foreach(unit_id_new[it]) {
		        unit_id_new[it][sv_dma_bus_pack::DMA_REQUEST_UNITID_W-1 -: $clog2(DMA_PORTS)] == 0;
            }
	    }
    };

    constraint c_max_request_size {
        max_request_size dist {
            `ndk_rand_dist_first(1, PCIE_MAX_REQUEST_SIZE, 8)    :/ 20,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 1) :/ 5,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 2) :/ 2,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 3) :/ 1,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 4) :/ 1,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 5) :/ 2,
            `ndk_rand_dist      (1, PCIE_MAX_REQUEST_SIZE, 8, 6) :/ 5,
            `ndk_rand_dist_last (1, PCIE_MAX_REQUEST_SIZE, 8)    :/ 20
        };
    }

    constraint c_max_payload_size {
        max_payload_size dist {
            `ndk_rand_dist_first(1, PCIE_MAX_PAYLOAD_SIZE, 8)    :/ 20,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 1) :/ 5,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 2) :/ 2,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 3) :/ 1,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 4) :/ 1,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 5) :/ 2,
            `ndk_rand_dist      (1, PCIE_MAX_PAYLOAD_SIZE, 8, 6) :/ 5,
            `ndk_rand_dist_last (1, PCIE_MAX_PAYLOAD_SIZE, 8)    :/ 20
        };
    }

    function new(string name = "uvm_dma::sequence_dma_rq");
        super.new(name);
    endfunction

    task body;
        assert(uvm_config_db #(uvm_dma::seq_info)::get(m_sequencer, "", "info", info)) else begin
            `uvm_fatal(m_sequencer != null ? m_sequencer.get_full_name() : "", "\n\tCannot get tag manager");
        end;

        req = uvm_dma::sequence_item_rq::type_id::create("req", m_sequencer);

        for (int unsigned it = 0; it < transactions; it++) begin
            int unsigned unit_id;
            int unsigned unit_id_old[];
            logic [8-1:0] tags[];

            //GET UNIT ID
            unit_id_old = info.tags.find_index() with (1);
            assert(std::randomize(unit_id) with {
                if (unit_id_old.size() > 0) {
                    unit_id dist   {unit_id_new :/ 80, unit_id_old :/ 20};
                } else {
                    unit_id inside {unit_id_new};
                }
            }) else begin
                `uvm_fatal(this.get_full_name(), "\n\tCannot randomize unit id")
            end

            //GET USED TAGS
            if (info.tags.exists(unit_id)) begin
                wait(info.tags[unit_id].size() < 256);
            end else begin
                info.tags[unit_id].delete();
            end
            tags = info.tags[unit_id].find_index() with (1);

            start_item(req);

            assert(req.randomize() with {
                req.type_ide dist { 0 :/ type_ide_read, 1 :/ type_ide_write};
                req.unitid == unit_id;
                (req.type_ide == 0) -> !(req.tag inside {tags});
                req.length == 1 -> (unsigned'(req.firstib) + unsigned'(req.lastib)) < 4;
                //req.firstib inside {0};
                //req.lastib  inside {0};
                req.length > 0;
                (req.type_ide == 1) -> req.length <= max_payload_size;
                (req.type_ide == 0) -> req.length <= max_request_size;
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tsequence_dma_rq cannot randomize");
            end

            if (req.type_ide == 0) begin
                info.tag_add(unit_id, req.tag);
            end
            finish_item(req);
        end
    endtask
endclass


class sequence_dma_rq_stop#(
    int unsigned DMA_PORTS
) extends uvm_common::sequence_base#(config_sequence, uvm_dma::sequence_item_rq);
    `uvm_object_param_utils(uvm_dma::sequence_dma_rq#(DMA_PORTS))

    time wait_time_min = 40ns;
    time wait_time_max = 10us;
    rand time wait_time;

    constraint c_max_payload_size {
        wait_time dist {
            `ndk_rand_dist_first(wait_time_min, wait_time_max, 8)    :/ 30,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 1) :/ 64,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 2) :/ 32,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 3) :/ 16,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 4) :/ 8,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 5) :/ 4,
            `ndk_rand_dist      (wait_time_min, wait_time_max, 8, 6) :/ 2,
            `ndk_rand_dist_last (wait_time_min, wait_time_max, 8)    :/ 1
        };
    }

    function new(string name = "mi_cc_sequence");
        super.new(name);
    endfunction

    task body;
        #(wait_time);
    endtask
endclass

class sequence_dma_rq_lib #(
    int unsigned DMA_PORTS
) extends uvm_common::sequence_library#(config_sequence, uvm_dma::sequence_item_rq);
  `uvm_object_param_utils(uvm_dma::sequence_dma_rq_lib#(DMA_PORTS))
  `uvm_sequence_library_utils(uvm_dma::sequence_dma_rq_lib#(DMA_PORTS))

    function new(string name = "sequence_lib_rx");
        super.new(name);
        init_sequence_library();
    endfunction

    // subclass can redefine and change run sequences
    // can be useful in specific tests
    virtual function void init_sequence(config_sequence param_cfg = null);
        uvm_common::sequence_library::init_sequence(param_cfg);
        this.add_sequence(uvm_dma::sequence_dma_rq_stop#(DMA_PORTS)::get_type());
        this.add_sequence(uvm_dma::sequence_dma_rq#(DMA_PORTS)::get_type());
    endfunction
endclass


