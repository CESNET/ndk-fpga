/*
 * file       : sequence_search.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: generatet packet with packet protocols
 * date       : 2022
 * author     : Radek Isa <isa@censet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


// Reusable high level sequence. Contains transaction, which has only data part.
class sequence_search #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base#(config_sequence, uvm_logic_vector_array::sequence_item#(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_packet_generators::sequence_search#(ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer#(ITEM_WIDTH));

    int unsigned pkt_size_min = 60;
    int unsigned pkt_size_max = 0;
    string config_json = "./filter.json";
    rand int unsigned transaction_count;
    rand int unsigned pkt_gen_seed;
    int unsigned transaction_count_min = 100;
    int unsigned transaction_count_max = 200;

    //randomization packet
    //ETH next protocol  (IPV4, IPV6, VLAN, MPLS, Empty, PPP)
    rand int unsigned eth_next_prot[6];
    rand int unsigned vlan_next_prot[6];
    rand int unsigned ppp_next_prot[4];
    rand int unsigned mpls_next_prot[4];
    rand int unsigned ipv4_next_prot[5];
    rand int unsigned ipv6_next_prot[6];
    rand int unsigned proto_next_prot[2]; //empty/payload
    rand int unsigned algorithm; // 0 -> rand; 1 -> dfs

    rand int unsigned packet_err_prob; //empty/payload

    constraint c_alg{
        algorithm dist {0 :/ 10, 1 :/ 1};
    }

    constraint c_err {
        packet_err_prob dist {[0:10] :/ 70, [11:70] :/ 20, [71:99] :/ 10};
    };

    constraint c_eth{
        foreach(eth_next_prot[it]) {
            eth_next_prot[it] >= 0;
            eth_next_prot[it]  < 10;
        }
        eth_next_prot.sum() > 0;
    };

    constraint c_vlan{
        foreach(vlan_next_prot[it]) {
            vlan_next_prot[it] >= 0;
            vlan_next_prot[it]  < 10;
        }
        vlan_next_prot.sum() > 0;
    };

    constraint c_ppp{
        foreach(ppp_next_prot[it]) {
            ppp_next_prot[it] >= 0;
            ppp_next_prot[it]  < 10;
        }
        ppp_next_prot.sum() > 0;
    };

    constraint c_mpls{
        foreach(mpls_next_prot[it]) {
            mpls_next_prot[it] >= 0;
            mpls_next_prot[it]  < 10;
        }
        mpls_next_prot.sum() > 0;
    };

    constraint c_ipv4{
        foreach(ipv4_next_prot[it]) {
            ipv4_next_prot[it] >= 0;
            ipv4_next_prot[it]  < 10;
        }
        ipv4_next_prot.sum() > 0;
    };

    constraint c_ipv6{
        foreach(ipv6_next_prot[it]) {
            ipv6_next_prot[it] >= 0;
            ipv6_next_prot[it]  < 10;
        }
        ipv6_next_prot.sum() > 0;
    };

    constraint c_proto{
        foreach(proto_next_prot[it]) {
            proto_next_prot[it] >= 0;
            proto_next_prot[it]  < 10;
        }
        proto_next_prot.sum() > 0;
    };

    constraint c1 {transaction_count inside {[transaction_count_min : transaction_count_max]};}

    // Constructor - creates new instance of this class
    function new(string name = "sequence_search");
        super.new(name);
        cfg = new();

        //pkt_gen_file =  $system({"`dirname ", FILE_PATH, "../pkt_gen/pkt_gen.py"});
    endfunction

    function string proto_dist_gen(int unsigned weight[], string proto[]);
        string ret = "";
        if (weight.size() != proto.size()) begin
            `uvm_fatal(p_sequencer.get_full_name(), $sformatf(" \n\uvm_packet_generators::sequence_search#(%0d) weight(%0d) and proto(%0d) size is not same", ITEM_WIDTH, weight.size(), proto.size()));
        end
        for(int unsigned it = 0; it < weight.size(); it++) begin
            if (it != 0) begin
                ret = {ret, $sformatf(", \"%s\" : %0d",  proto[it], weight[it])};
            end else begin
                ret = $sformatf("\"%s\" : %0d", proto[it], weight[it]);
            end
        end
        return {"{", ret ,"}"};
    endfunction

    function void configure(string file_json);
        int file;
        string rule_ipv6 = {"\t{ \"min\" : \"0x00000000000000000000000000000000\", \"max\" : \"0xffffffffffffffffffffffffffffffff\" }", generate_ipv6_rule()};
        string rule_ipv4 = {"\t{ \"min\" : \"0x00000000\", \"max\" : \"0xffffffff\" }", generate_ipv4_rule()};

        // create json configuration for pkt_gen
        if((file = $fopen(file_json, "w")) == 0) begin
            `uvm_fatal(this.get_full_name(), $sformatf("\n\t Cannot open file %s for writing", file_json));
        end
        $fwrite(file, "{\n");
        //ETH
        $fwrite(file, "\"packet\" : { \"err_probability\" : %0d},\n", packet_err_prob);
        $fwrite(file, "\"ETH\"  : { \"weight\" : %s},\n", proto_dist_gen(eth_next_prot, {"IPv4", "IPv6", "VLAN", "MPLS", "Empty", "PPP"}));
        $fwrite(file, "\"VLAN\" : { \"weight\" : %s},\n", proto_dist_gen(vlan_next_prot, {"IPv4", "IPv6", "VLAN", "MPLS", "Empty", "PPP"}));
        $fwrite(file, "\"PPP\" : { \"weight\" : %s},\n",  proto_dist_gen(ppp_next_prot, {"IPv4", "IPv6", "MPLS", "Empty"}));
        $fwrite(file, "\"MPLS\" : { \"weight\" : %s},\n", proto_dist_gen(mpls_next_prot, {"IPv4", "IPv6", "MPLS", "Empty"}));
        $fwrite(file, "\"TCP\" : { \"weight\" : %s},\n",  proto_dist_gen(proto_next_prot, {"Empty", "Payload"}));
        $fwrite(file, "\"UDP\" : { \"weight\" : %s},\n",  proto_dist_gen(proto_next_prot, {"Empty", "Payload"}));

        $fwrite(file, "\"IPv4\" : { \"values\" : {");
        $fwrite(file, {"\n\t\"src\" : ", "[\n", rule_ipv4, "],", "\n\t\"dst\" : ", "[\n", rule_ipv4, "]"});
        $fwrite(file, "\n\t},\n\t\"weight\" : %s},\n", proto_dist_gen(ipv4_next_prot, {"Payload", "Empty", "ICMPv4", "UDP", "TCP"}));

        $fwrite(file, "\"IPv6\" : { \"values\" : {");
        $fwrite(file, {"\n\t\"src\" : ", "[\n", rule_ipv6, "],", "\n\t\"dst\" : ", "[\n", rule_ipv6, "]"});
        $fwrite(file, "\n\t},\n\t\"weight\" : %s},\n", proto_dist_gen(ipv6_next_prot, {"Payload", "Empty", "ICMPv4", "UDP", "TCP", "IPv6Ext"}));

        $fwrite(file, "\"IPv6Ext\" : { \"weight\" : %s}\n", proto_dist_gen(ipv6_next_prot, {"Payload", "Empty", "ICMPv4", "UDP", "TCP", "IPv6Ext"}));

        $fwrite(file, "\n\t}\n");
        $fclose(file);
    endfunction

    function string generate_ipv4_rule();
        string rule = "";
        foreach (cfg.ipv4_addresses[i]) begin
            rule = { rule, ",\n\t", ipv4_print(cfg.ipv4_addresses[i], 32) };
        end
        return rule;
    endfunction

    function string ipv4_print(logic [32-1:0] ip_min, int unsigned length);
        logic [32-1:0] ip_mask;

        ip_mask = '0;
        for (int unsigned it = 0; it < length; it++) begin
            ip_mask[32-1 - it] = 1;
        end
        return $sformatf("{ \"min\" : \"0x%h\", \"max\" : \"0x%h\" }", ip_min & ip_mask, ip_min | ~ip_mask);
    endfunction

    function string generate_ipv6_rule();
        string rule = "";
        foreach (cfg.ipv6_addresses[i]) begin
            rule = { rule, ",\n\t", ipv6_print(cfg.ipv4_addresses[i], 128) };
        end
        return rule;
    endfunction

    function string ipv6_print(logic [128-1:0] ip_min, int unsigned length);
        logic [128-1:0] ip_mask;

        ip_mask = '0;
        for (int unsigned it = 0; it < length; it++) begin
            ip_mask[128-1 - it] = 1;
        end
        return $sformatf("{ \"min\" : \"0x%h\", \"max\" : \"0x%h\" }", ip_min & ip_mask, ip_min | ~ip_mask);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        uvm_pcap::reader reader;
        byte unsigned    data[];
        int unsigned     pkt_num = 0;

        string pcap_file = "test.pcap";
        string pkt_gen_params;

        reader = new();
        if (!uvm_config_db #(string)::get(p_sequencer, "", "pcap_file", pcap_file)) begin
            pcap_file = {p_sequencer.get_full_name(), ".pcap"};
        end


        `uvm_info(get_full_name(), $sformatf("\n\tsequence_search is running\n\t\tpcap_name%s", pcap_file), UVM_DEBUG);

        this.configure(config_json);
        pkt_gen_params = $sformatf("-a %s -f \"%s\" -p %0d -c %s -s %0d", algorithm == 0 ? "rand" : "dfs",  pcap_file, transaction_count, config_json, pkt_gen_seed);
        if($system({PKT_GEN_PATH, " ", pkt_gen_params, " >> pkt_gen_out"}) != 0) begin
            `uvm_fatal(p_sequencer.get_full_name(), $sformatf("\n\t Cannot run command %s", {PKT_GEN_PATH, " ", pkt_gen_params}))
        end

        void'(reader.open(pcap_file));
        req = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("req", p_sequencer);
        while(reader.read(data) == uvm_pcap::RET_OK)
        begin
            pkt_num++;
            // Generate random request, which must be in interval from min length to max length
            start_item(req);
            if (data.size() < pkt_size_min) begin
                data = new[pkt_size_min](data);
            end
            if (pkt_size_max > 0 && data.size() > pkt_size_max) begin
                data = new[pkt_size_max](data);
            end
            req.data = {>>{data}};
            finish_item(req);
        end
        reader.close();
    endtask

endclass



