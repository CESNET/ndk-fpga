// probe_csb.sv: probe's callback with discard logic based on the Mask and SOF signals
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

class probe_cbs #(int unsigned REGIONS) extends uvm_event_callback;
    `uvm_object_param_utils(frame_masker::probe_cbs #(REGIONS))

    protected logic [1-1:0] out_discard[$];

    function new(string name = "");
        super.new(name);
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e, uvm_object data);
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------

    virtual function void post_trigger(uvm_event e, uvm_object data);
        uvm_probe::data#(2*REGIONS) c_data;
        int unsigned highest_mask_index_found = 0;
        logic [REGIONS-1 : 0] discard;
        int unsigned discard_cnt = 0; // counts current Discards and is also used as index to store them

        logic [REGIONS-1 : 0] sof;
        logic [REGIONS-1 : 0] mask;

        // $write("Probe POST_TRIGGER\n");

        $cast(c_data, data);
        {sof, mask} = c_data.data;

        // For multiple Regions, some packets can be skipped (=discarded)
        if (REGIONS > 1) begin
            // when there is at least one SOF and one Mask, set Discard appropriately
            if (|sof & |mask == 1) begin
                for (int unsigned r = REGIONS; r > 0;) begin
                    r--;
                    if (sof[r] == 1) begin
                        if (mask[r] == 1) begin
                            highest_mask_index_found = 1;
                            // using "discard_cnt" instead of "r" as index to shake down Discard values
                            discard[discard_cnt] = 0;
                            discard_cnt++; // shift index to store the next Discard
                        end
                        else if (highest_mask_index_found == 1) begin
                            discard[discard_cnt] = 1;
                            discard_cnt++; // shift index to store the next Discard
                        end
                    end
                end
            end

            // Store Discard values (only those that are valid) to output FIFO
            for (int r = discard_cnt; r > 0; r--) begin
                out_discard.push_back(discard[r-1]);
            end

        // For one Region, packets can't be skipped/discarded
        end else begin
            // for each SOF, send a discard=0 to the output
            if (sof[0] == 1) begin
                out_discard.push_back(0);
            end
        end

    endfunction

    //---------------------------------------
    // OTHERS METHODS
    //---------------------------------------
    task get_discard(output logic [1-1:0] discard);
        wait(out_discard.size() != 0);
        discard = out_discard.pop_front();
    endtask

    function int unsigned used();
        return (out_discard.size() != 0);
    endfunction
endclass
