// my_trans.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import crc32_ethernet_pkg::*;

class MyTransaction #(ITEM_WIDTH = 8) extends Transaction;

    rand bit [ITEM_WIDTH-1 : 0] data[];
    byte unsigned crc[3 : 0];
    bit error = 0;
    bit mintu_error = 0;
    bit maxtu_error = 0;
    bit mac_error = 0;
    rand bit crc_error;
    rand bit adapter_error;
    bit mac_mcast = 0;
    bit mac_bcast = 0;
    int dataSizeMax = 512;
    int dataSizeMin = 64;
    int mac_count = 0;
    int mac_type = 0;
    rand int mac_index;
    byte unsigned mac_array[16][6] = '{default: 0};

    constraint c1 {
        crc_error dist {1 := 5, 0 := 95};
        adapter_error dist {1 := 5, 0 := 95};
        data.size inside {[dataSizeMin:dataSizeMax]};
        mac_index inside {[0:mac_count-1]};
    };

    virtual function void display(string prefix = "");
        if(prefix != "") begin
            $write("---------------------------------------------------------\n");
            $write("-- %s\n",prefix);
            $write("---------------------------------------------------------\n");
        end
        //$write("Global Error Bit: %1d\n", error);
        $write("Adapter Error: %1d\n", adapter_error);
        $write("CRC Error: %1d (CRC value: %h %h %h %h)\n", crc_error, crc[0], crc[1], crc[2], crc[3]);
        $write("MaxTU Error: %1d, MinTU Error: %1d\n", maxtu_error, mintu_error);
        $write("MAC Error: %1d (MAC Multicast: %1d, MAC Broadcast: %1d, MAC index %1d)\n", mac_error, mac_mcast, mac_bcast, mac_index);
        $write("Frame size: %1d items, Data:", data.size);
        for(int j=0; j < data.size; j++) begin
            if(j%32==0) $write("\n\t");
            if(j%8==0) $write(" ");
            $write("%x ",data[j]);
        end
        $write("\n\n");
    endfunction

    virtual function Transaction copy(Transaction to = null);
        MyTransaction #(ITEM_WIDTH) tr;

        if (to == null)
            tr = new();
        else
            $cast(tr, to);

        tr.data = data;
        tr.crc = crc;
        tr.error = error;
        tr.adapter_error = adapter_error;
        tr.crc_error = crc_error;
        tr.maxtu_error = maxtu_error;
        tr.mintu_error = mintu_error;
        tr.mac_error = mac_error;
        tr.mac_mcast = mac_mcast;
        tr.mac_bcast = mac_bcast;
        tr.mac_count = mac_count;
        tr.mac_index = mac_index;
        tr.mac_array = mac_array;

        tr.dataSizeMax = dataSizeMax;
        tr.dataSizeMin = dataSizeMin;
        copy = tr;
    endfunction

    virtual function bit compare(input Transaction to, output string diff, input int kind = -1);
        MyTransaction #(ITEM_WIDTH) tr;
        $cast(tr, to);

        if (data != tr.data) begin
            if (data.size != tr.data.size) begin
                diff = $sformatf( "data size does not match");
            end else begin
                for (int j=0; j < data.size; j++) begin
                if (data[j] != tr.data[j]) begin
                    diff = $sformatf( "Items #%1d does not match", j);
                    break;
                end
                end
            end
            return 0;
        end

        if (adapter_error != tr.adapter_error) begin
            diff = "Adapter Error flag does not match";
            return 0;
        end

        if (maxtu_error != tr.maxtu_error) begin
            diff = "MaxTU Error flag does not match";
            return 0;
        end

        if (mintu_error != tr.mintu_error) begin
            diff = "MinTU Error flag does not match";
            return 0;
        end

        if (crc_error != tr.crc_error) begin
            diff = "CRC Error flag does not match";
            return 0;
        end

        if (mac_error != tr.mac_error) begin
            diff = "MAC Error flag does not match";
            return 0;
        end

        if (mac_bcast != tr.mac_bcast) begin
            diff = "MAC BROADCAST flag does not match";
            return 0;
        end

        if (mac_mcast != tr.mac_mcast) begin
            diff = "MAC MULTICAST flag does not match";
            return 0;
        end

        if ((mac_index != tr.mac_index) && mac_type == 1) begin
            diff = "MAC index does not match";
            return 0;
        end

        return 1;
    endfunction

    function void post_randomize();
        int index;
        int crc_offset;
        byte error_byte;
        bit [ITEM_WIDTH-1 : 0] data_without_crc[];
        bit [31:0] crc_value;

        // Insert correct MAC
        randcase
            1: begin // BROADCAST
                mac_type = 3;
                for (int i=0; i < 6; i++) begin
                    data[i] = 8'hFF;
                end
                mac_bcast = 1;
            end

            1: begin // MULTICAST
                mac_type = 2;
                data[0][0] = 1;
                mac_mcast = 1;
            end

            1: begin // AVAILABLE UNICAST
                if (mac_count > 0) begin
                    mac_type = 1;
                    for (int i=0; i<6; i++)
                        // Must be in network format (big endian) => MSB byte first!
                        data[i] = mac_array[mac_index][5-i];
                    end
                end

            1: ; // UNICAST
        endcase

        if (data.size() >= 4) begin
            crc_offset = data.size()-4;
            data_without_crc = new[crc_offset](data);

            // Compute correct CRC
            crc_value = ~crc32_ethernet(data_without_crc, 32'hffffffff);
            crc = {<< byte{crc_value}};

            if (crc_error) begin
                // Inject CRC Error
                assert(std::randomize(index, error_byte) with {
                    index inside { [0:3] };
                });
                if (crc[index] == error_byte) begin
                    crc[index] = ~error_byte;
                end else begin
                    crc[index] = error_byte;
                end
            end

            // Insert CRC to data
            for (int i = 0; i<4; i++) begin
                data[crc_offset+i] = crc[3-i];
            end
        end
    endfunction

endclass
