/*!
 * \file mfb_monitor.sv
 * \brief Monitor of Multi-Frame Bus
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



class MfbMonitor #(REGIONS = 4, REGION_SIZE = 8, BLOCK_SIZE = 8, ITEM_WIDTH = 8, META_WIDTH = 1, META_ALIGNMENT = 0) extends Monitor;
    // META_WIDTH defines width META signal in bits per region.
    // META_ALIGNMENT=0 => META signal is aligned with SOF, META_ALIGNMENT=1 => META signal is aligned with EOF.

    localparam ITEMS = REGIONS * REGION_SIZE * BLOCK_SIZE;
    localparam REGION_ITEMS = REGION_SIZE * BLOCK_SIZE;
    localparam SOF_POS_WIDTH = log2(REGION_SIZE);
    localparam EOF_POS_WIDTH = log2(REGION_SIZE * BLOCK_SIZE);
    typedef bit [ITEM_WIDTH-1 : 0] item;
    typedef bit [META_WIDTH-1 : 0] meta_item;

    int ref_gap_size_min          = 8;
    int ref_gap_size_avg          = 8;
    bit gap_size_check            = 0;
    int avg_gap_size_check_period = 100;

    local virtual iMfbTx#(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH).monitor vif;


    function new(string i, virtual iMfbTx#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH).monitor v);
        super.new(i);
        vif = v;
    endfunction

    virtual task run();
        Transaction transaction;
        MfbTransaction #(ITEM_WIDTH,META_WIDTH) tr;
        bit [ITEM_WIDTH-1 : 0] buffer[$], data[ITEMS];
        int i, j, start, offset, later, late, inframe, data_id, eof_checked, gap_size, avg_gap_size, total_gap, number_of_gaps;
        buffer = {};
        inframe = 0;
        offset = 0;
        data_id = 0;
        start = 0;
        eof_checked = 0;
        gap_size = 0;
        avg_gap_size = 0;
        total_gap = 0;
        number_of_gaps = 0;
        while(enabled) begin
            do begin
                @(vif.monitor_cb);
                busy = inframe || vif.monitor_cb.SRC_RDY;
                if(eof_checked == 1)
                    gap_size = gap_size + ITEMS;
            end while(enabled && !(vif.monitor_cb.SRC_RDY && vif.monitor_cb.DST_RDY)); // wait for valid data
            if(!enabled) break;
            if(start) begin // clean old data from buffer
                buffer = {buffer[start : $]};
                offset = offset - start;
                start = 0;
            end
            data = { << item {vif.monitor_cb.DATA} };
            buffer = {buffer, data};
            if(!vif.monitor_cb.SOF && !vif.monitor_cb.EOF) begin // nothing important in this word
                if(!inframe) begin
                    $write("@%0t - %s: Error in MFB protocol! Valid data outside frame.\n", $time, inst);
                    @(vif.monitor_cb);
                    $stop();
                end
                offset = offset + ITEMS;
                if(eof_checked == 1)
                    gap_size += ITEMS;
            end else // some SOF or EOF => process them
                for(j=0; j < REGIONS; j++, offset = offset+REGION_ITEMS) begin
                    if(SOF_POS_WIDTH && vif.monitor_cb.SOF[j] && vif.monitor_cb.EOF[j]) begin // SOF and EOF in the same region
                        later = (vif.monitor_cb.SOF_POS[j*SOF_POS_WIDTH +: SOF_POS_WIDTH] * BLOCK_SIZE) > vif.monitor_cb.EOF_POS[j*EOF_POS_WIDTH +: EOF_POS_WIDTH];
                        gap_size += REGION_ITEMS - (REGION_ITEMS - vif.monitor_cb.EOF_POS[j*EOF_POS_WIDTH +: EOF_POS_WIDTH]) + ((vif.monitor_cb.SOF_POS[j*SOF_POS_WIDTH +: SOF_POS_WIDTH] * BLOCK_SIZE) + 1);
                    end else
                        later = 0; // EOF after SOF in the region
                    late = 0;
                    do begin
                        if(vif.monitor_cb.SOF[j] && !later) begin // SOF processing
                            if(inframe) begin
                                $write("@%0t - %s: Error in MFB protocol! SOF detected inside frame in region #%1d.\n", $time, inst, j);
                                @(vif.monitor_cb);
                                $stop();
                            end else begin
                                inframe = 1;
                                tr = new;
                                tr.data_id = data_id;
                                data_id = data_id + 1;
                                $cast(transaction, tr);
                                foreach(cbs[i]) cbs[i].pre_rx(transaction, inst);
                                tr.sof = j;
                                if(META_ALIGNMENT == 0)
                                    tr.meta = vif.monitor_cb.META[j*META_WIDTH +: META_WIDTH];
                                if(SOF_POS_WIDTH) begin
                                    start = offset + (vif.monitor_cb.SOF_POS[j*SOF_POS_WIDTH +: SOF_POS_WIDTH] * BLOCK_SIZE);
                                    tr.sof_pos = vif.monitor_cb.SOF_POS[j*SOF_POS_WIDTH +: SOF_POS_WIDTH];
                                    gap_size += (vif.monitor_cb.SOF_POS[j*SOF_POS_WIDTH +: SOF_POS_WIDTH] * BLOCK_SIZE);
                                end else begin
                                    start = offset;
                                    tr.sof_pos = 0;
                                end
                                if(gap_size_check == 1) begin
                                    if(eof_checked == 1) begin
                                    	if(gap_size <= 2*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH) begin // Ignore very large gaps
                                        	total_gap += gap_size;
                                        	number_of_gaps += 1;
                                        end
                                        if(!(gap_size >= ref_gap_size_min)) begin // Gap processing
                                            $write("@%0t - %s: Error in MFB protocol! Gap between packets is less then minimal value.\n", $time, inst);
                                            $write("Gap size         %d\n", gap_size);
                                            $write("Minimal gap size %d\n", ref_gap_size_min);
                                            @(vif.monitor_cb);
                                            $stop();
                                        end
                                        if(number_of_gaps == avg_gap_size_check_period) begin
                                            avg_gap_size = total_gap/number_of_gaps;
                                            if(!(avg_gap_size >= ref_gap_size_avg)) begin // Average gap processing
                                                $write("@%0t - %s: Error in MFB protocol! Average gap is less then reference average gap.\n", $time, inst);
                                                $write("Average gap size           %d\n", avg_gap_size);
                                                $write("Reference average gap size %d\n", ref_gap_size_avg);
                                                @(vif.monitor_cb);
                                                $stop();
                                            end
                                            number_of_gaps = 0;
                                            total_gap = 0;
                                        end
                                        gap_size = 0;
                                        eof_checked = 0;
                                    end
                                end
                            end
                        end
                        if(vif.monitor_cb.EOF[j] & !late) begin // EOF processing
                            if(inframe) begin
                                if(EOF_POS_WIDTH) begin
                                    tr.data = buffer[start : (offset+vif.monitor_cb.EOF_POS[j*EOF_POS_WIDTH +: EOF_POS_WIDTH])];
                                    gap_size += REGION_ITEMS - vif.monitor_cb.EOF_POS[j*EOF_POS_WIDTH +: EOF_POS_WIDTH] + 1;
                                end else begin
                                    tr.data = buffer[start : offset];
                                end
                                if(META_ALIGNMENT == 1)
                                    tr.meta = vif.monitor_cb.META[j*META_WIDTH +: META_WIDTH];
                                foreach(cbs[i]) cbs[i].post_rx(transaction, inst);
                                inframe = 0;
                                eof_checked = 1;
                            end else begin
                                $write("@%0t - %s: Error in MFB protocol! EOF detected outside frame in region #%1d.\n", $time, inst, i);
                                @(vif.monitor_cb);
                                $stop();
                            end
                        end
                        late = later; later = 0;
                    end while(late);
                    if(!vif.monitor_cb.EOF[j] && !vif.monitor_cb.SOF[j])
                        if(eof_checked == 1)
                            gap_size += REGION_ITEMS;
                end
        end
    endtask

endclass
