/* pcie_sequencer.sv
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Martin Spinler <spinler@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;

let min(a,b) = (a < b) ? a : b;

class PcieCompletionSequencer #(RCB = 64, MPS = 256) extends Driver;

    parameter CLK_PERIOD    = 10ns;

    int verbosity;
    tag_manager tags_save;

    function new(string inst, tTransMbx transMbx, tag_manager tags_save);
        super.new(inst, transMbx);
        this.tags_save = tags_save;
    endfunction

    function void verbosity_set(int unsigned level);
        verbosity = level;
    endfunction

    virtual task run();
        int i;
        time t;
        Transaction tr;
        PcieCompletion from;

        PcieCompletion comp_splitted[$];
        PcieCompletion comp_pending[$];
        time time_pending[$];

        while (enabled) begin
            while (transMbx.try_get(tr)) begin
                $cast(from, tr);

                comp_splitted = {};
                t = $time;

                split(from, comp_splitted);
                while (comp_splitted.size()) begin
                    from = comp_splitted.pop_front();
                    /* Randomize send time for each completion. Keep sequence of parts */
                    t += $urandom_range(10, 0) * CLK_PERIOD;

                    /* Compute index to queue - sort by time */
                    for (i = 0; i < time_pending.size(); i++)
                        if (t < time_pending[i])
                            break;

                    /* Add completion to pending queues */
                    time_pending.insert(i, t);
                    comp_pending.insert(i, from);
                end
            end

            if (time_pending.size() && time_pending[0] <= $time) begin
                t = time_pending.pop_front();

                from = comp_pending.pop_front();
                tr = from;

//                $writeh("Sending data: %p\n", from.data);

                if (from.completed == 1) begin
                    tags_save.remove(from.tag);
                end
                foreach (cbs[i])
                    cbs[i].pre_tx(tr, inst);
                /* No-op = virtual driver */
                foreach (cbs[i])
                    cbs[i].post_tx(tr, inst);
            end else begin
                #(CLK_PERIOD);
            end
        end
    endtask

    virtual task split(PcieCompletion from, ref PcieCompletion completions[$]);
        int rcbs;
        int index;
        int unsigned l;
        int unsigned length;
        logic [6:0] address;
        int unsigned comp_length;
        int unsigned byte_count;

        PcieCompletion comp;

        address = from.lower_address;
        length = from.length;
        index = 0;
        byte_count = from.byte_count;

        while (length) begin
            /* Generate number of RCB blocks for this completion (between 1 and all remaining RCB for read request) */
            rcbs = $urandom_range((length + (address[6:2] & (RCB/4-1)) + RCB/4-1) / (RCB/4), 1);

            /* Always use first segment: align to RCB */
            comp_length = min(RCB/4 - (address[6:2] & (RCB/4-1)), length);

            /* Compute maximal allowed length of current transaction */
            for (int i = 1; i < rcbs; i++) begin
                /* Select smaller value between RCB and remaining length of request */
                l = min(RCB/4, length - comp_length);

                /* Completion length must be at most MPS */
                if (comp_length + l > MPS/4)
                    break;

                comp_length += l;
            end

            comp = new();
            comp.length = comp_length;
            comp.tag = from.tag;
            comp.completed = (comp_length == length);
            comp.requester_id = from.requester_id;
            comp.data = new[comp.length];
            for (int i = 0; i < comp.length; i++)
                comp.data[i] = from.data[index + i];
            comp.lower_address = address[6:0];
            comp.byte_count    = byte_count;
            byte_count -= (comp_length*4 - address[1:0]);
            if (verbosity)
                comp.display({inst, " Completion"});
                //$writeh("Completion addr: %x, len: %x, tag: %x, length: %x, completed: %x: data: %p\n", address, comp_length, comp.tag, comp.length, comp.completed, comp.data);

            index += comp.length;
            length -= comp_length;
            address[6:2] += comp_length;
            address[1:0] = 2'b00;
            completions.push_back(comp);
        end
    endtask
endclass
