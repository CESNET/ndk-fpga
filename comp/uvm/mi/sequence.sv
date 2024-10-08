/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: mi sequence
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

//////////////////////////////////////////////////////////////////////////////////
// SLAVE SEQUENCE
//////////////////////////////////////////////////////////////////////////////////
class sequence_slave #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequence#(sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_mi::sequence_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))
    `uvm_declare_p_sequencer(sequencer_slave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH ));

    int unsigned rd_count;
    int unsigned rsp_count;

    int unsigned transactions_min = 10;
    int unsigned transactions_max = 200;
    rand int unsigned transactions;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
    }

    function new (string name = "sequence_slave");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("req");
        rd_count  = 0;
        rsp_count = 0;
        use_response_handler(1);
        repeat(transactions) begin
            start_item(req);
            if(req.randomize() == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave cannot randomize");
            end
            finish_item(req);

            if (req.rd == 1) begin
                rd_count++;
            end
        end

        wait (rd_count == rsp_count);
    endtask

    function void response_handler(uvm_sequence_item response);
        rsp_count++;
    endfunction
endclass

class sequence_slave_same_addr #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_slave#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_slave_same_addr #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    rand logic [DATA_WIDTH-1:0] rand_addr;

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("req");
        rd_count  = 0;
        rsp_count = 0;
        use_response_handler(1);

        repeat(transactions) begin
            start_item(req);
            if(req.randomize() with {addr == rand_addr;} == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave_same_addr cannot randomize");
            end
            finish_item(req);

            if (req.rd == 1) begin
                rd_count++;
            end
        end

        wait (rd_count == rsp_count);
    endtask
endclass

class sequence_slave_incr_addr #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_slave#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_slave_incr_addr #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    rand logic [DATA_WIDTH-1:0] rand_addr;
    rand int unsigned           increment_size;
    rand bit                    increment; //0 decrement, 1 increment
    int unsigned                increment_size_min = 1;
    int unsigned                increment_size_max = 10;

    constraint c_increment_size {
        increment_size inside {[increment_size_min:increment_size_max]};
    }

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("req");
        rd_count  = 0;
        rsp_count = 0;
        use_response_handler(1);

        repeat(transactions) begin
            start_item(req);
            if(req.randomize() with {addr == rand_addr;} == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave_incr_addr cannot randomize");
            end

            if (increment == 1) begin
                // increment addres by size of data in bytes
                rand_addr += increment_size*DATA_WIDTH/8;
            end else begin
                // decrement addres by size of data in bytes
                rand_addr -= increment_size*DATA_WIDTH/8;
            end
            finish_item(req);

            if (req.rd == 1) begin
                rd_count++;
            end
        end

        wait (rd_count == rsp_count);
    endtask
endclass

class sequence_slave_burst #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_slave#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_slave_burst #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    rand logic [ADDR_WIDTH-1:0] addr_min;
    rand logic [ADDR_WIDTH-1:0] addr_max;
    rand logic [2-1:0] type_tr; // 0x01 => READ, 0x02 => WR

    constraint c_sequence {
        addr_min < addr_max;
    }

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("req");
        rd_count  = 0;
        rsp_count = 0;
        use_response_handler(1);

        repeat(transactions) begin
            int unsigned rand_req;
            start_item(req);
            rand_req = req.randomize() with {addr inside {[addr_min:addr_max]};
                                              (type_tr == 2'b00) -> ((rd == 0) && (wr == 0));
                                              (type_tr == 2'b01) -> ((rd == 1) && (wr == 0));
                                              (type_tr == 2'b10) -> ((rd == 0) && (wr == 1));
                                            };
            if (rand_req == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave_burst cannot randomize");
            end
            finish_item(req);

            if (req.rd == 1) begin
                rd_count++;
            end
        end

        wait (rd_count == rsp_count);
    endtask
endclass

class sequence_slave_sim #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_slave#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_slave_sim #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    uvm_mi::sequence_item_response #(DATA_WIDTH) mi_tr_fifo [$];

    function new (string name = "sequence_slave_sim");
        super.new(name);
    endfunction

    function void response_handler(uvm_sequence_item response);
        uvm_mi::sequence_item_response #(DATA_WIDTH) rsp;
        super.response_handler(response);

        $cast(rsp, response);
        mi_tr_fifo.push_back(rsp);
    endfunction

    task get_rsp(output uvm_mi::sequence_item_response #(DATA_WIDTH) rsp);
        wait(mi_tr_fifo.size() != 0);
        rsp = mi_tr_fifo.pop_front();
    endtask

    // Task that allow you to create your own MI write transaction
    task write(logic [ADDR_WIDTH-1:0] addr, logic [DATA_WIDTH-1:0] dwr, logic [DATA_WIDTH/8-1:0] be = '1);

        do begin
            start_item(req);
            req.wr   = 1'b1;
            req.rd   = 1'b0;
            req.dwr  = dwr;
            req.addr = addr;
            req.be   = be;
            finish_item(req);
        end while (req.ardy === '0);

    endtask

    // Task that allow you to create your own MI read transaction
    task read(logic [ADDR_WIDTH-1:0] addr, logic [DATA_WIDTH/8-1:0] be = '1);

        do begin
            start_item(req);
            req.wr   = 1'b0;
            req.rd   = 1'b1;
            req.dwr  = 'x;
            req.addr = addr;
            req.be   = be;
            finish_item(req);
        end while (req.ardy === '0);

        rd_count++;

        wait (rd_count == rsp_count);

    endtask

    virtual task create_sequence_item();
    endtask

    // In body you have to define how the MI transaction will look like
    task body;
        req = uvm_mi::sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::type_id::create("req");
        use_response_handler(1);

        create_sequence_item();

    endtask

endclass


class sequence_slave_library #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequence_library#(sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_mi::sequence_slave_library#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))
    `uvm_sequence_library_utils(uvm_mi::sequence_slave_library#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))


    function new(string name = "");
        super.new(name);
        init_sequence_library();

        this.min_random_count = 100;
        this.max_random_count = 500;

        this.add_sequence(uvm_mi::sequence_slave#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mi::sequence_slave_same_addr#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mi::sequence_slave_incr_addr#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mi::sequence_slave_burst#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass


////////////////////////////////////////////////////////////////////////////////////
// Master SEQUENCE
////////////////////////////////////////////////////////////////////////////////////
class sequence_master #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequence#(sequence_item_response #(DATA_WIDTH), sequence_item_request #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH));
    `uvm_object_param_utils(uvm_mi::sequence_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))
    `uvm_declare_p_sequencer(sequencer_master #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH ));

    int unsigned transactions_min = 10;
    int unsigned transactions_max = 200;
    rand int unsigned transactions;

    constraint c_transactions {
        transactions inside {[transactions_min:transactions_max]};
    }

    function new (string name = "sequence_request");
        super.new(name);
    endfunction

    task save_request();
        logic reset;
        if (rsp.ardy == 1'b1) begin
            sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tr_resp;
            $cast(tr_resp, rsp.clone());
            p_sequencer.tr_rd.push_back(tr_resp);
        end

        if (req.drdy) begin
            p_sequencer.tr_rd.pop_front();
        end

        if (p_sequencer.sync.has_been_reset()) begin
            p_sequencer.tr_rd.delete();
        end
    endtask

    task body;
        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        repeat(transactions) begin
            start_item(req);
            if(req.randomize() with {(p_sequencer.tr_rd.size() == 0) -> drdy == 0;} == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_master cannot randomize");
            end
            finish_item(req);

            get_response(rsp);
            save_request();
        end
    endtask
endclass


class sequence_master_burst #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_master#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_master_burst#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    rand logic [2-1:0] type_tr; // 0x01 => READ, 0x02 => WR

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        repeat(transactions) begin
            int unsigned rand_req;
            start_item(req);
            rand_req = req.randomize() with {
                                    (type_tr[0] == 1'b0) -> drdy == 0;
                                    (type_tr[0] == 1'b1) -> (p_sequencer.tr_rd.size() == 0) -> drdy == 0;
                                    (type_tr[0] == 1'b1) -> (p_sequencer.tr_rd.size() != 0) -> drdy == 1;
                                    (type_tr[1] == 1'b0) -> ardy == 0;
                                    (type_tr[1] == 1'b1) -> ardy == 1;
                                 };

            if (rand_req == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave_master_burst cannot randomize");
            end
            finish_item(req);

            get_response(rsp);
            save_request();
        end
    endtask
endclass

class sequence_master_max #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends sequence_master#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH);
    `uvm_object_param_utils(uvm_mi::sequence_master_max#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))

    function new (string name = "sequence_reset");
        super.new(name);
    endfunction

    task body;
        req = sequence_item_response #(DATA_WIDTH)::type_id::create("req");
        repeat(transactions) begin
            int unsigned rand_req;
            start_item(req);
            rand_req = req.randomize() with {
                                   (p_sequencer.tr_rd.size() != 0) -> drdy == 1;
                                   (p_sequencer.tr_rd.size() == 0) -> drdy == 0;
                                    ardy == 1;
                                 };
            if (rand_req == 0) begin
                `uvm_fatal(p_sequencer.get_full_name(), "sequence_slave_master_max cannot randomize");
            end
            finish_item(req);

            get_response(rsp);
            save_request();
        end
    endtask
endclass


class sequence_master_library #(int unsigned DATA_WIDTH, int unsigned ADDR_WIDTH, int unsigned META_WIDTH = 0) extends uvm_sequence_library#(sequence_item_request#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH), sequence_item_response #(DATA_WIDTH));
    `uvm_object_param_utils(uvm_mi::sequence_master_library#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))
    `uvm_sequence_library_utils(uvm_mi::sequence_master_library#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH))


    function new(string name = "");
        super.new(name);
        init_sequence_library();

        this.min_random_count = 100;
        this.max_random_count = 500;

        this.add_sequence(uvm_mi::sequence_master#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mi::sequence_master_burst#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
        this.add_sequence(uvm_mi::sequence_master_max#(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)::get_type());
    endfunction
endclass

