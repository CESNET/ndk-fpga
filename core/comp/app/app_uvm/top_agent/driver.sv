//-- driver.sv: Clone packet transaction to mfb and mvb
//-- Copyright (C) 2024 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause 


class driver#(ITEM_WIDTH, META_WIDTH) extends uvm_driver #(sequence_item#(ITEM_WIDTH, META_WIDTH));
    `uvm_component_param_utils(uvm_app_core_top_agent::driver#(ITEM_WIDTH, META_WIDTH))

    //RESET reset_sync
    uvm_reset::sync_terminate reset_sync;

    typedef enum {
        STORE_MVB,
        STORE_MFB
    } store_diff_type;

    config_item m_config;
    protected sequence_item#(ITEM_WIDTH, META_WIDTH) fifo_mvb_tmp[$];
    protected sequence_item#(ITEM_WIDTH, META_WIDTH) fifo_mfb_tmp[$];
    protected uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo_mvb;
    protected uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)) fifo_mfb;

    // Contructor, where analysis port is created.
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        reset_sync = new();
    endfunction: new


    function int unsigned used();
        int unsigned ret = 0;
        ret |= (fifo_mvb_tmp.size() != 0);
        ret |= (fifo_mfb_tmp.size() != 0);
        ret |= (fifo_mvb.size() != 0);
        ret |= (fifo_mfb.size() != 0);
        return ret;
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task run_fifo_tmp();
        sequence_item#(ITEM_WIDTH, META_WIDTH) gen;
        forever begin

            //In case of RESET  delete all data from MVB and MFB
            wait((fifo_mvb_tmp.size() == 0   || fifo_mfb_tmp.size() == 0) || reset_sync.is_reset());
            if (reset_sync.has_been_reset()) begin

                fifo_mvb_tmp.delete();
                fifo_mfb_tmp.delete();

                while(reset_sync.has_been_reset() != 0) begin
                    #(40ns);
                end
            end

            // GET packet item and divide it
            // to MVB item and MFB item
            seq_item_port.get_next_item(req);
            $cast(gen, req.clone());

            fifo_mvb_tmp.push_back(gen);
            fifo_mfb_tmp.push_back(gen);
            seq_item_port.item_done();
        end
    endtask

    task run_fifo();
        sequence_item#(ITEM_WIDTH, META_WIDTH) gen;
        int unsigned diff;
        int unsigned diff_count;
        store_diff_type diff_type;
        time end_time;
        //time max_wait;

        diff_count = 0;
        forever begin
            time end_time;

            if (diff_count == 0) begin
                const int unsigned diff_step = (m_config.diff_max - m_config.diff_min)/10;
                assert(std::randomize(diff_type, diff, diff_count) with
                    {
                        diff_type  dist { STORE_MVB := m_config.weigth_mfb_first, 1'b1, STORE_MFB := m_config.weigth_mvb_first};
                        diff       dist { [m_config.diff_min              : m_config.diff_min + diff_step] :/ 95,
                                          [m_config.diff_min+ diff_step   : m_config.diff_min + diff_step*9] :/ 1,
                                          [m_config.diff_min+ diff_step*9 : m_config.diff_max] :/ 5};
                        diff_count dist { [m_config.diff_count_min:m_config.diff_count_max] };
                    })
                    else begin
                        `uvm_fatal(this.get_full_name(), "\n\tCannot randomize diff type");
                    end
            end else begin
                diff_count--;
            end

            // Diff and diff_count. Select randomly if MVB or MFB is going ot be ahed of the other.
            // There is timeout if application cannot received enough data on MVB interface or MFB interface
            wait(fifo_mvb_tmp.size() != 0 && fifo_mfb_tmp.size() != 0);
            if (diff_type == STORE_MVB) begin
                //MFB is generated first
                end_time = $time() + 300ns;
                wait(fifo_mfb.size() == 0 || (fifo_mvb.size() == 0 && end_time < $time()));
                if (diff < fifo_mvb_tmp.size() || fifo_mfb_tmp.size() > 0) begin
                    gen = fifo_mvb_tmp.pop_front();
                    fifo_mvb.push_back(gen);
                end
                gen = fifo_mfb_tmp.pop_front();
                fifo_mfb.push_back(gen);
            end else if (diff_type == STORE_MFB) begin
                //MVB is generated first
                end_time = $time() + 300ns;
                wait(fifo_mvb.size() == 0 || (fifo_mfb.size() == 0 && end_time < $time()));
                if (diff < fifo_mfb_tmp.size() || fifo_mvb_tmp.size() > 0) begin
                    gen = fifo_mfb_tmp.pop_front();
                    fifo_mfb.push_back(gen);
                end
                gen = fifo_mvb_tmp.pop_front();
                fifo_mvb.push_back(gen);
            end else begin
                `uvm_fatal(this.get_full_name(), $sformatf("\n\tUnknown diff type %s", diff_type));
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        assert (uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::get(this, "", "fifo_mvb", fifo_mvb)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get mvb fifo");
        end

        assert (uvm_config_db#(uvm_common::fifo#(sequence_item#(ITEM_WIDTH, META_WIDTH)))::get(this, "", "fifo_mfb", fifo_mfb)) else begin
            `uvm_fatal(this.get_full_name(), "\n\tCannot get mfb fifo");
        end

        fork
            run_fifo_tmp();
            run_fifo();
        join
    endtask
endclass

