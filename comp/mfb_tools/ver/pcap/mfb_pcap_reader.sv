/*
 * mfb_pcap_reader.sv: Multi-Frame Bus reader of PCAP files (can be used instead of generator)
 * Copyright (C) 2016 CESNET z. s. p. o.
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package sv_mfb_pcap;

    import dpi_pcap::*;
    import sv_mfb_pkg::*;
    import sv_common_pkg::*;



    class MfbPcapReader extends Generator;

        // PcapReader does not use transation blueprint, instead, it needs path to PCAP file.
        string pcap_file;

        function new(string inst, int stream_id = -1, tTransMbx transMbx = null);
            super.new(inst, stream_id, transMbx);
        endfunction

        virtual task run();
            MfbTransaction #(8) trans;
            dpi_pcap_t pcap;
            dpi_pcap_pkthdr_t hdr;
            pcap = dpi_pcap_open_offline(pcap_file);
            if(pcap) begin
                // While is enabled or stop = 0 or number of generated transactions not exceed limit
                while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin
                    trans = new;
                    if(dpi_pcap_next_ex(pcap, hdr, trans.data) != 1) // PCAP file ended
                        break;
                    trans.stream_id    = stream_id;       // Set stream id
                    trans.scenario_id  = -1;              // Set default scenario
                    trans.data_id      = data_id;         // Set instance count
                    transMbx.put(trans);                  // Put transaction to mailbox
                    data_id=data_id+1;                    // Increment instance counter
                end;
                dpi_pcap_close(pcap);
            end
            enabled = 0;
        endtask

    endclass

endpackage
