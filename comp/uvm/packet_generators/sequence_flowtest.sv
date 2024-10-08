// sequence_flowtest.sv: Generated packet sequence that uses FlowTest ft-generator (https://github.com/CESNET/FlowTest/tree/main/tools/ft-generator)
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

class sequence_flowtest #(int unsigned ITEM_WIDTH) extends uvm_common::sequence_base #(config_sequence, uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
    `uvm_object_param_utils(uvm_packet_generators::sequence_flowtest #(ITEM_WIDTH))
    `uvm_declare_p_sequencer(uvm_logic_vector_array::sequencer #(ITEM_WIDTH));

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

    // ================= //
    // Random parameters //
    // ================= //

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
    function new(string name = "sequence_flowtest");
        super.new(name);

        cfg = new();
    endfunction

    function void configure();
        foreach (cfg.ipv4_addresses[i]) begin
            ipv4 = new[ipv4.size()+1](ipv4);
            ipv4[ipv4.size()-1].address = cfg.ipv4_addresses[i];
            ipv4[ipv4.size()-1].mask = 32;
        end

        foreach (cfg.ipv6_addresses[i]) begin
            ipv6 = new[ipv6.size()+1](ipv6);
            ipv6[ipv6.size()-1].address = cfg.ipv6_addresses[i];
            ipv6[ipv6.size()-1].mask = 128;
        end
    endfunction

    function string get_ipv4_addresses();
        string ipv4_addresses = "";
        string ipv4_address;

        foreach (ipv4[i]) begin
            ipv4_address = $sformatf("%0d.%0d.%0d.%0d/32",
                            ipv4[i].address[31 : 24],
                            ipv4[i].address[23 : 16],
                            ipv4[i].address[15 : 8],
                            ipv4[i].address[7 : 0]);

            if (ipv4_addresses == "") begin
                ipv4_addresses = ipv4_address;
            end
            else begin
                ipv4_addresses = { ipv4_addresses, ";", ipv4_address };
            end
        end

        return ipv4_addresses;
    endfunction

    function string get_ipv6_addresses();
        string ipv6_addresses = "";
        string ipv6_address;

        foreach (ipv6[i]) begin
            ipv6_address = $sformatf("%04h:%04h:%04h:%04h:%04h:%04h:%04h:%04h/128",
                            ipv6[i].address[127 : 112],
                            ipv6[i].address[111 : 96],
                            ipv6[i].address[95 : 80],
                            ipv6[i].address[79 : 64],
                            ipv6[i].address[63 : 48],
                            ipv6[i].address[47 : 32],
                            ipv6[i].address[31 : 16],
                            ipv6[i].address[15 : 0]);

            if (ipv6_addresses == "") begin
                ipv6_addresses = ipv6_address;
            end
            else begin
                ipv6_addresses = { ipv6_addresses, ";", ipv6_address };
            end
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
        config_generator_execute_command = { CONFIG_GENERATOR_EXECUTE_PATH, " ", config_generator_parameters }; // Creating string of the config generator call command

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
        profile_generator_execute_command = { PROFILE_GENERATOR_EXECUTE_PATH, " ", profile_generator_parameters }; // Creating string of the profile generator call command

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

        // Output configuration options
        string output_filepath = "output.pcap";
        string report_filepath = "report.txt";
        bit skip_unknown = 0;
        bit no_collision_check = 1;

        string generator_parameters;
        string generator_execute_command;

        configure();
        generate_tools_configuration();

        reader = new();
        if (!uvm_config_db #(string)::get(p_sequencer, "", "output_filepath", output_filepath)) begin
            output_filepath = { p_sequencer.get_full_name(), ".pcap" };
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
        generator_execute_command = { GENERATOR_EXECUTE_PATH, " ", generator_parameters }; // Creating string of the generator call command

        assert($system(generator_execute_command) == 0) else begin
            `uvm_fatal(p_sequencer.get_full_name(), $sformatf("\n\t Cannot run command %s", generator_execute_command))
        end

        void'(reader.open(output_filepath)); // Try open an output pcap

        req = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("req", p_sequencer);
        while(reader.read(data) == uvm_pcap::RET_OK) begin
            start_item(req);
            req.data = { >>{ data } };
            finish_item(req);
        end

        reader.close();
    endtask

endclass
