/*
 * file       : sequence_eth.sv
 * Copyright (C) 2024 CESNET z. s. p. o.
 * description: verification sequence for ethernet
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/


class sequence_eth#(
    int unsigned CHANNELS,
    int unsigned LENGTH_WIDTH,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base #(config_sequence_eth, uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_app_core::sequence_eth#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))

    int unsigned transaction_min = 100;
    int unsigned transaction_max = 300;
    rand int unsigned   transactions;

    constraint c_transactions {
        transactions inside {[transaction_min:transaction_max]};
    }

    // Constructor - creates new instance of this class
    function new(string name = "sequence");
        super.new(name);
    endfunction

    // -----------------------
    // Functions.
    // -----------------------
    task body;
        int unsigned it;
        uvm_common::sequence_cfg state;

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        req = uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::type_id::create("req", m_sequencer);
        while (it < transactions && (state == null || !state.stopped())) begin
            logic [32-1:0] time_act_sec;
            logic [32-1:0] time_act_nano_sec;
            logic [64-1:0] time_sim = (cfg.time_start + $time())/1ns;

            time_act_nano_sec = time_sim%1000000000;
            time_act_sec      = time_sim/1000000000;

            //generat new packet
            start_item(req);
            assert (req.randomize() with {
                req.data.size() inside {[60:1500]};
                req.timestamp_vld dist { 1'b1 :/ 80, 1'b0 :/20};
                req.timestamp_vld -> req.timestamp == {time_act_sec, time_act_nano_sec};
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize uvm_app_core_top_agent::sequence_eth_item");
            end
            finish_item(req);
            it++;
        end
    endtask
endclass



class sequence_flowtest_eth #(
    int unsigned CHANNELS,
    int unsigned LENGTH_WIDTH,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base #(config_sequence_eth, uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_app_core::sequence_flowtest_eth #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))

    // Packet size configuration options
    int unsigned forward_packet_number_min = 10;
    int unsigned forward_packet_number_max = 100;

    int unsigned reverse_packet_number_min = 10;
    int unsigned reverse_packet_number_max = 100;

    // IPv4 configuration options
    int unsigned ipv4_number_min = 2;
    int unsigned ipv4_number_max = 10;

    int unsigned ipv4_mask_min = 16;
    int unsigned ipv4_mask_max = 32;

    // IPv6 configuration options
    int unsigned ipv6_number_min = 2;
    int unsigned ipv6_number_max = 10;

    int unsigned ipv6_mask_min = 64;
    int unsigned ipv6_mask_max = 128;

    // MAC configuration options
    int unsigned mac_number_min = 2;
    int unsigned mac_number_max = 10;

    int unsigned mac_mask_min = 24;
    int unsigned mac_mask_max = 48;

    // Generator options
    logic generated_config = 1;
    logic generated_profile = 1;

    string config_filepath = "./config.yaml";
    string profile_filepath = "./profile.csv";

    string config_generator_config_filepath = "";
    string profile_generator_config_filepath = "";

    // ------------- //
    // PACKET NUMBER //
    // ------------- //

    rand int unsigned forward_packet_number;
    rand int unsigned reverse_packet_number;

    constraint c_forward_packet_number { forward_packet_number inside { [forward_packet_number_min : forward_packet_number_max] }; }
    constraint c_reverse_packet_number { reverse_packet_number inside { [reverse_packet_number_min : reverse_packet_number_max] }; }

    // ------------- //
    // IPv4 ADRESSES //
    // ------------- //

    typedef struct {
        rand bit [31 : 0] address;
        rand int unsigned mask;
    } ipv4_t;

    rand ipv4_t ipv4[];

    constraint c_ipv4_number { ipv4.size() inside { [ipv4_number_min : ipv4_number_max] }; }
    constraint c_ipv4_mask {
        foreach (ipv4[i]) {
            ipv4[i].mask inside { [ipv4_mask_min : ipv4_mask_max] };
        }
    }

    // ------------- //
    // IPv6 ADRESSES //
    // ------------- //

    typedef struct {
        rand bit [127 : 0] address;
        rand int unsigned mask;
    } ipv6_t;

    rand ipv6_t ipv6[];

    constraint c_ipv6_number { ipv6.size() inside { [ipv6_number_min : ipv6_number_max] }; }
    constraint c_ipv6_mask {
        foreach (ipv6[i]) {
            ipv6[i].mask inside { [ipv6_mask_min : ipv6_mask_max] };
        }
    }

    // ------------ //
    // MAC ADRESSES //
    // ------------ //

    typedef struct {
        rand bit [47 : 0] address;
        rand int unsigned mask;
    } mac_t;

    rand mac_t mac[];

    constraint c_mac_number { mac.size() inside { [mac_number_min : mac_number_max] }; }
    constraint c_mac_mask {
        foreach (mac[i]) {
            mac[i].mask inside { [mac_mask_min : mac_mask_max] };
        }
    }

    rand int unsigned seed;

    // Constructor
    function new(string name = "sequence_flowtest_eth");
        super.new(name);

        cfg = new();
    endfunction

    //function void configure();
    //    //foreach (cfg.ipv4_addresses[i]) begin
    //    //    ipv4 = new[ipv4.size()+1](ipv4);
    //    //    ipv4[ipv4.size()-1].address = cfg.ipv4_addresses[i];
    //    //    ipv4[ipv4.size()-1].mask = 32;
    //    //end

    //    //foreach (cfg.ipv6_addresses[i]) begin
    //    //    ipv6 = new[ipv6.size()+1](ipv6);
    //    //    ipv6[ipv6.size()-1].address = cfg.ipv6_addresses[i];
    //    //    ipv6[ipv6.size()-1].mask = 128;
    //    //end
    //endfunction

    function string get_ipv4_addresses();
        string ipv4_addresses = "";
        string sep = "";

        foreach (ipv4[i]) begin
            const string ipv4_address = $sformatf("%0d.%0d.%0d.%0d/%0d",
                            ipv4[i].address[31 : 24],
                            ipv4[i].address[23 : 16],
                            ipv4[i].address[15 : 8],
                            ipv4[i].address[7 : 0],
                            ipv4[i].mask);

            ipv4_addresses = { ipv4_addresses, sep, ipv4_address };
            sep = ";";
        end

        foreach (cfg.ipv4_addresses[i]) begin
            const string ipv4_address = $sformatf("%0d.%0d.%0d.%0d/%0d",
                            cfg.ipv4_addresses[i][31 : 24],
                            cfg.ipv4_addresses[i][23 : 16],
                            cfg.ipv4_addresses[i][15 : 8],
                            cfg.ipv4_addresses[i][7 : 0],
                            30);

            ipv4_addresses = { ipv4_addresses, sep, ipv4_address };
            sep = ";";
        end

        return ipv4_addresses;
    endfunction

    function string get_ipv6_addresses();
        string ipv6_addresses = "";
        string sep = "";

        foreach (ipv6[i]) begin
            const string ipv6_address = $sformatf("%04h:%04h:%04h:%04h:%04h:%04h:%04h:%04h/%0d",
                            ipv6[i].address[127 : 112],
                            ipv6[i].address[111 : 96],
                            ipv6[i].address[95 : 80],
                            ipv6[i].address[79 : 64],
                            ipv6[i].address[63 : 48],
                            ipv6[i].address[47 : 32],
                            ipv6[i].address[31 : 16],
                            ipv6[i].address[15 : 0],
                            ipv6[i].mask
                        );

            ipv6_addresses = { ipv6_addresses, sep, ipv6_address };
            sep = ";";
        end

        foreach (cfg.ipv6_addresses[i]) begin
            const string ipv6_address = $sformatf("%04h:%04h:%04h:%04h:%04h:%04h:%04h:%04h/%0d",
                            cfg.ipv6_addresses[i][127 : 112],
                            cfg.ipv6_addresses[i][111 : 96],
                            cfg.ipv6_addresses[i][95 : 80],
                            cfg.ipv6_addresses[i][79 : 64],
                            cfg.ipv6_addresses[i][63 : 48],
                            cfg.ipv6_addresses[i][47 : 32],
                            cfg.ipv6_addresses[i][31 : 16],
                            cfg.ipv6_addresses[i][15 : 0],
                            126
                        );

            ipv6_addresses = { ipv6_addresses, sep, ipv6_address };
            sep = ";";
        end

        return ipv6_addresses;
    endfunction

    function string get_mac_addresses();
        string mac_addresses = "";
        string mac_address;

        foreach (mac[i]) begin
            mac_address = $sformatf("%02h:%02h:%02h:%02h:%02h:%02h/48",
                            mac[i].address[47 : 40],
                            mac[i].address[39 : 32],
                            mac[i].address[31 : 24],
                            mac[i].address[23 : 16],
                            mac[i].address[15 : 8],
                            mac[i].address[7 : 0]);

            if (mac_addresses == "") begin
                mac_addresses = mac_address;
            end
            else begin
                mac_addresses = { mac_addresses, ";", mac_address };
            end
        end

        return mac_addresses;
    endfunction

    function void generate_config();
        string config_generator_parameters;
        string config_generator_execute_command;
        string ipv4_addresses = get_ipv4_addresses();
        string ipv6_addresses = get_ipv6_addresses();
        string mac_addresses  = get_mac_addresses();

        config_generator_parameters = $sformatf("-o \"%s\" --seed %0d %s %s %s %s", // Creating string of the options
                                       config_filepath,
                                       seed,
                                       (config_generator_config_filepath != "") ? { "--config \"", config_generator_config_filepath, "\"" } : "",
                                       (ipv4_addresses != "") ? { "--ipv4 \"", ipv4_addresses, "\"" } : "",
                                       (ipv6_addresses != "") ? { "--ipv6 \"", ipv6_addresses, "\"" } : "",
                                       (mac_addresses != "") ? { "--mac \"", mac_addresses, "\"" } : "");
        config_generator_execute_command = { uvm_packet_generators::CONFIG_GENERATOR_EXECUTE_PATH, " ", config_generator_parameters }; // Creating string of the config generator call command

        // Try generate config file
        assert ($system(config_generator_execute_command) == 0) else begin // Try execute
            `uvm_fatal(get_full_name(), $sformatf("\n\t Cannot run command %s", config_generator_execute_command))
        end
    endfunction

    function void generate_profile();
        string profile_generator_parameters;
        string profile_generator_execute_command;

        profile_generator_parameters = $sformatf("-o \"%s\" --seed %0d %s --forward-packet-number %0d --reverse-packet-number %0d", // Creating string of the options
                                        profile_filepath,
                                        seed,
                                        (profile_generator_config_filepath != "") ? { "--config \"", profile_generator_config_filepath, "\"" } : "",
                                        forward_packet_number,
                                        reverse_packet_number);
        profile_generator_execute_command = { uvm_packet_generators::PROFILE_GENERATOR_EXECUTE_PATH, " ", profile_generator_parameters }; // Creating string of the profile generator call command

        // Try generate profile file
        assert($system(profile_generator_execute_command) == 0) else begin // Try execute
            `uvm_fatal(get_full_name(), $sformatf("\n\t Cannot run command %s", profile_generator_execute_command))
        end
    endfunction

    function void generate_tools_configuration();
        if (generated_config) begin
            generate_config();
        end
        if (generated_profile) begin
            generate_profile();
        end
    endfunction

    // Sequence main body
    task body;
        uvm_pcap::reader reader;
        byte unsigned    data[];
        uvm_common::sequence_cfg state;

        // Output configuration options
        string output_filepath = "output.pcap";
        string report_filepath = "report.txt";
        bit skip_unknown = 0;
        bit no_collision_check = 1;

        string generator_parameters;
        string generator_execute_command;

        //configure();
        generate_tools_configuration();

        reader = new();
        if (!uvm_config_db #(string)::get(m_sequencer, "", "output_filepath", output_filepath)) begin
            output_filepath = { m_sequencer.get_full_name(), ".pcap" };
        end

        `uvm_info(get_full_name(), $sformatf("\n\tsequence_flowtest is running\n\t\tpcap_name%s", output_filepath), UVM_DEBUG);

        generator_parameters = $sformatf("-p %s -c %s -o \"%s\" -r %s --seed %0d %s %s", // Creating string of the options
                                profile_filepath,
                                config_filepath,
                                output_filepath,
                                report_filepath,
                                seed,
                                (skip_unknown ? "--skip-unknown" : ""),
                                (no_collision_check ? "--no-collision-check" : ""));
        generator_execute_command = { uvm_packet_generators::GENERATOR_EXECUTE_PATH, " ", generator_parameters }; // Creating string of the generator call command

        assert($system(generator_execute_command) == 0) else begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("\n\t Cannot run command %s", generator_execute_command))
        end


        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        void'(reader.open(output_filepath)); // Try open an output pcap
        req = uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::type_id::create("req", m_sequencer);
        while( reader.read(data) == uvm_pcap::RET_OK && (state == null || !state.stopped())) begin
            logic [32-1:0] time_act_sec;
            logic [32-1:0] time_act_nano_sec;
            logic [64-1:0] time_sim = (cfg.time_start + $time())/1ns;

            time_act_nano_sec = time_sim%1000000000;
            time_act_sec      = time_sim/1000000000;

            start_item(req);
            assert (req.randomize() with {
                req.timestamp_vld dist { 1'b1 :/ 80, 1'b0 :/20};
                req.timestamp_vld -> req.timestamp == {time_act_sec, time_act_nano_sec};
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize uvm_app_core_top_agent::sequence_eth_item");
            end

            req.data = { >>{ data } };
            finish_item(req);
        end

        reader.close();
    endtask

endclass


class sequence_search_eth  #(
    int unsigned CHANNELS,
    int unsigned LENGTH_WIDTH,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_base #(config_sequence_eth, uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH));
    `uvm_object_param_utils(uvm_app_core::sequence_search_eth#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))

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
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf(" \n\uvm_packet_generators::sequence_search#(%0d) weight(%0d) and proto(%0d) size is not same", ITEM_WIDTH, weight.size(), proto.size()));
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
            rule = { rule, ",\n\t", ipv6_print(cfg.ipv6_addresses[i], 126) };
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
        uvm_common::sequence_cfg state;

        string pcap_file = "test.pcap";
        string pkt_gen_params;

        reader = new();
        if (!uvm_config_db #(string)::get(m_sequencer, "", "pcap_file", pcap_file)) begin
            pcap_file = {m_sequencer.get_full_name(), ".pcap"};
        end


        `uvm_info(get_full_name(), $sformatf("\n\tsequence_search is running\n\t\tpcap_name%s", pcap_file), UVM_DEBUG);

        this.configure(config_json);
        pkt_gen_params = $sformatf("-a %s -f \"%s\" -p %0d -c %s -s %0d", algorithm == 0 ? "rand" : "dfs",  pcap_file, transaction_count, config_json, pkt_gen_seed);
        if($system({uvm_packet_generators::PKT_GEN_PATH, " ", pkt_gen_params, " >> pkt_gen_out"}) != 0) begin
            `uvm_fatal(m_sequencer.get_full_name(), $sformatf("\n\t Cannot run command %s", {uvm_packet_generators::PKT_GEN_PATH, " ", pkt_gen_params}))
        end

        if(!uvm_config_db#(uvm_common::sequence_cfg)::get(m_sequencer, "", "state", state)) begin
            state = null;
        end

        void'(reader.open(pcap_file));
        req = uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::type_id::create("req", m_sequencer);
        while(reader.read(data) == uvm_pcap::RET_OK && (state == null || !state.stopped())) begin
            logic [32-1:0] time_act_sec;
            logic [32-1:0] time_act_nano_sec;
            logic [64-1:0] time_sim = (cfg.time_start + $time())/1ns;

            time_act_nano_sec = time_sim%1000000000;
            time_act_sec      = time_sim/1000000000;

            pkt_num++;
            // Generate random request, which must be in interval from min length to max length
            start_item(req);

            assert (req.randomize() with {
                req.timestamp_vld dist { 1'b1 :/ 80, 1'b0 :/20};
                req.timestamp_vld -> req.timestamp == {time_act_sec, time_act_nano_sec};
            }) else begin
                `uvm_fatal(m_sequencer.get_full_name(), "\n\tCannot randomize uvm_app_core_top_agent::sequence_eth_item");
            end

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





class sequence_library_eth #(
    int unsigned CHANNELS,
    int unsigned LENGTH_WIDTH,
    int unsigned ITEM_WIDTH
) extends uvm_common::sequence_library #(config_sequence_eth, uvm_app_core_top_agent::sequence_eth_item#(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH));
    `uvm_object_param_utils(    uvm_app_core::sequence_library_eth #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))
    `uvm_sequence_library_utils(uvm_app_core::sequence_library_eth #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH))

    function new(string name = "packet_generator_sequence_library");
        super.new(name);
        init_sequence_library();
    endfunction

    virtual function void init_sequence(config_sequence_eth param_cfg = null);
        super.init_sequence(param_cfg);

        this.add_sequence(sequence_eth          #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_search_eth   #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::get_type());
        this.add_sequence(sequence_flowtest_eth #(CHANNELS, LENGTH_WIDTH, ITEM_WIDTH)::get_type());
    endfunction

endclass
