//-- model.sv: model 
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class drop_cbs #(string ETH_CORE_ARCH, int unsigned ETH_PORT_SPEED) extends uvm_event_callback;
    `uvm_object_param_utils(uvm_network_mod_env::drop_cbs #(ETH_CORE_ARCH, ETH_PORT_SPEED))

    localparam int unsigned REGIONS_CORE = (ETH_PORT_SPEED == 400) ? 2 : 1;
    localparam int unsigned RESIZED_REGIONS = (ETH_CORE_ARCH == "F_TILE") ? 2*REGIONS_CORE : REGIONS_CORE;

    logic queue[$];

    function new(string name = "drop_cbs");
        super.new(name);
    endfunction

    //---------------------------------------
    // pre trigger method
    //---------------------------------------
    virtual function bit pre_trigger(uvm_event e, uvm_object data);
        return 0;
    endfunction

    //---------------------------------------
    // post trigger method
    //---------------------------------------
    virtual function void post_trigger(uvm_event e, uvm_object data);
        uvm_probe::data#(2*RESIZED_REGIONS) c_data;
        logic [RESIZED_REGIONS-1:0] pkt_eof;
        logic [RESIZED_REGIONS-1:0] pkt_drop;

        $cast(c_data, data);
        {pkt_eof, pkt_drop} = c_data.data;
        
        for (int unsigned it = 0; it < RESIZED_REGIONS; it++) begin
            if (pkt_eof[it] == 1) begin
                queue.push_back(pkt_drop[it]);
            end
        end
    endfunction

    task get(output logic drop);
        wait(queue.size() != 0);
        drop = queue.pop_front();
    endtask
endclass


class model #(string ETH_CORE_ARCH, int unsigned ETH_PORTS, int unsigned ETH_PORT_SPEED[ETH_PORTS-1:0], int unsigned ETH_PORT_CHAN[ETH_PORTS-1:0], REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH) extends uvm_component;
    `uvm_component_param_utils(uvm_network_mod_env::model #(ETH_CORE_ARCH, ETH_PORTS, ETH_PORT_SPEED, ETH_PORT_CHAN, REGIONS, ITEM_WIDTH, ETH_TX_HDR_WIDTH, ETH_RX_HDR_WIDTH));

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) eth_rx_data[ETH_PORTS];
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(6))                eth_rx_hdr [ETH_PORTS];
    uvm_analysis_port    #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) eth_tx_data[ETH_PORTS];
    uvm_analysis_port    #(uvm_logic_vector::sequence_item#(1))                eth_tx_hdr[ETH_PORTS];

    uvm_tlm_analysis_fifo#(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) usr_rx_data[ETH_PORTS];
    uvm_tlm_analysis_fifo#(uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH)) usr_rx_hdr [ETH_PORTS];
    uvm_analysis_port    #(uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)) usr_tx_data[ETH_PORTS];
    uvm_analysis_port    #(uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH)) usr_tx_hdr[ETH_PORTS];

    //SYNCHRONIZATION 
    protected drop_cbs #(ETH_CORE_ARCH, ETH_PORT_SPEED[0]) drop_sync[ETH_PORTS][];

    protected int unsigned eth_recv[ETH_PORTS];
    protected int unsigned eth_drop[ETH_PORTS];

    // Constructor of environment.
    function new(string name, uvm_component parent);
        super.new(name, parent);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            eth_rx_data[it] = new($sformatf("eth_rx_data_%0d", it), this);
            eth_rx_hdr [it] = new($sformatf("eth_rx_hdr_%0d", it), this);
            eth_tx_data[it] = new($sformatf("eth_tx_data_%0d", it), this);
            eth_tx_hdr [it] = new($sformatf("eth_tx_hdr_%0d", it), this);

            usr_rx_data[it] = new($sformatf("usr_rx_data_%0d", it), this);
            usr_rx_hdr [it] = new($sformatf("usr_rx_hdr_%0d", it), this);
            usr_tx_data[it] = new($sformatf("usr_tx_data_%0d", it), this);
            usr_tx_hdr [it] = new($sformatf("usr_tx_hdr_%0d", it), this);

            eth_recv[it] = 0;
            eth_drop[it] = 0;
        end
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
         for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            ret |= (eth_rx_data[it].used() != 0);
            ret |= (eth_rx_hdr [it].used() != 0);
            ret |= (usr_rx_data[it].used() != 0);
            ret |= (usr_rx_hdr [it].used() != 0);
        end

        return ret;
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            drop_sync[it] = new[ETH_PORT_CHAN[it]];
            for (int unsigned jt = 0; jt < ETH_PORT_CHAN[it]; jt++) begin
               drop_sync[it][jt] = drop_cbs #(ETH_CORE_ARCH, ETH_PORT_SPEED[0])::type_id::create("drop_sync", this);
            end
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            for (int unsigned jt = 0; jt < ETH_PORT_CHAN[it]; jt++) begin
                uvm_probe::pool::get_global_pool().get({"probe_event_component_", $sformatf("testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[%0d].network_mod_logic_i.rx_g[%0d].rx_mac_g.rx_mac_i.buffer_i", it, jt), ".probe_drop"}).add_callback(drop_sync[it][jt]);
            end
        end
    endfunction

    task automatic run_eth(int unsigned index);
        uvm_logic_vector::sequence_item#(6)                 hdr;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)  data;

        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data_out;
        uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH) hdr_out;

        forever begin
            int unsigned channel;
            logic [16-1:0] length;
            logic [8-1:0]  port;
            logic [1-1:0]  error;
            logic [1-1:0]  error_frame;
            logic [1-1:0]  error_min_tu;
            logic [1-1:0]  error_max_tu;
            logic [1-1:0]  error_crc;
            logic [1-1:0]  error_mac;
            logic [1-1:0]  broadcast;
            logic [1-1:0]  multicast;
            logic [1-1:0]  mac_hit_vld;
            logic [4-1:0]  mac_hit;
            logic [1-1:0]  timestamp_vld;
            logic [64-1:0] timestamp;
            logic drop;
            logic [48-1:0]  dst_mac;
            logic [48-1:0]  src_mac;
            logic [16-1:0]  eth_type;
            string msg;

            eth_rx_hdr[index].get(hdr);
            eth_rx_data[index].get(data);

            `uvm_info(this.get_full_name(), {$sformatf("\n\tReceived %0d data to port[%0d]", eth_recv[index], index), hdr.convert2string(), data.convert2string()}, /*UVM_FULL*/ UVM_FULL)

            eth_recv[index]++;
            length = data.size();
            port   = index;

            channel = 0;
            if (ETH_PORT_CHAN[index] > 1) begin
                //channel = 'x;
                `uvm_fatal(this.get_full_name(), "\n\tChannels is not implemented!!")
            end
            {dst_mac, src_mac, eth_type} = {>>{data.data[0: (48+48+16)/ITEM_WIDTH-1]}};

            error_frame  = !is_frame_valid(hdr.data);
            error_min_tu = length < 60;
            error_max_tu = length > 1526;
            error_crc    = 0;
            error_mac    = 0;
            error = error_frame | error_min_tu | error_max_tu | error_crc | error_mac;

            broadcast = dst_mac === '1;
            multicast = (dst_mac[48-8] === 1) && !broadcast;

            //mac_hit_vld = 0;
            //mac_hit     = 'X;
            mac_hit_vld = 0;
            mac_hit     = 0;

            timestamp_vld = 1'b0;
            timestamp     = 'x;

            drop_sync[index][channel].get(drop);
            drop |= error_frame | error_min_tu | error_max_tu | error_crc | error_mac;

            msg = $sformatf("\n\thdr input time %s", hdr.time2string());
            msg = {msg, $sformatf("\n\tlength        [%0d]" , length)};
            msg = {msg, $sformatf("\n\terror         [0x%h]", error)};
            msg = {msg, $sformatf("\n\terror frame   [0x%h]", error_frame)};
            msg = {msg, $sformatf("\n\terror min MTU [0x%h]", error_min_tu)};
            msg = {msg, $sformatf("\n\terror max MTU [0x%h]", error_max_tu)};
            msg = {msg, $sformatf("\n\terror CRC     [0x%h]", error_crc)};
            msg = {msg, $sformatf("\n\terror MAC     [0x%h]", error_mac)};
            msg = {msg, $sformatf("\n\tbroadcast     [0x%h]", broadcast)};
            msg = {msg, $sformatf("\n\tmulticast     [0x%h]", multicast)};
            msg = {msg, $sformatf("\n\tMAC HIT VLD   [0x%h]", mac_hit_vld)};
            msg = {msg, $sformatf("\n\tMAC HIT       [0x%h]", mac_hit)};
            msg = {msg, $sformatf("\n\ttimestamp VLD [0x%h]", timestamp_vld)};
            msg = {msg, $sformatf("\n\ttimestamp     [0x%h]", timestamp)};
            msg = {msg, data.convert2string()};
            `uvm_info(this.get_full_name(), msg, UVM_MEDIUM);

            if (!drop) begin
                //crc_value = ~crc32_ethernet(mfbTrans.data, 32'hffffffff); nebylo by lepší?? crc_value = crc32_ethernet(mfbTrans.data, 32'h0);
                //crc = {<< byte{crc_value}};

                hdr_out = uvm_logic_vector::sequence_item#(ETH_RX_HDR_WIDTH)::type_id::create("hdr_out", this);
                hdr_out.start[$sformatf("ETH_RX[%0d]", index)] = $time();
                hdr_out.tag = "USR_TX";
                hdr_out.data = {timestamp, timestamp_vld, mac_hit, mac_hit_vld, multicast, broadcast, error_mac, error_crc, error_max_tu, error_min_tu, error_frame, error, port, length};

                data_out = data;
                //data_out = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("data_out", this);
                //data_out.start[$sformatf("ETH_RX[%0d]", index)] = $time();
                //data_out.tag = "USR_TX";
                //data_out.data = data.data;
                //data_out = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("data_out", this);
                //data_out.data = new[data.data.size()-4](data.data); //remove CRC

                usr_tx_data[index].write(data_out);
                usr_tx_hdr[index].write(hdr_out);
                //`uvm_info(this.get_full_name(), $sformatf("\nUSR RX [%0d] OUTPUT\nHEADER%s\nDATA%s\n", index, hdr_out.convert2string(), data_out.convert2string()), UVM_FULL);
                `uvm_info(this.get_full_name(), $sformatf("\n\tUSR RX [%0d] ACCEPT: Received %0d dropped %0d accepted %0d\n", index, eth_recv[index], eth_drop[index], eth_recv[index] - eth_drop[index]), UVM_MEDIUM);
            end else begin
                eth_drop[index]++;
                `uvm_info(this.get_full_name(), $sformatf("\n\tUSR RX [%0d] DROP: Received %0d dropped %0d accepted %0d\n", index, eth_recv[index], eth_drop[index], eth_recv[index] - eth_drop[index]), UVM_MEDIUM);
            end
       end
    endtask

    task automatic run_usr (int unsigned index);
        uvm_logic_vector::sequence_item#(ETH_TX_HDR_WIDTH) hdr;
        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data;

        uvm_logic_vector_array::sequence_item#(ITEM_WIDTH) data_out;
        uvm_logic_vector::sequence_item#(1)                hdr_out;

        // TX pošle paket pouze pokud je větší jak 60B
        forever begin
            logic [16-1:0] length;
            logic [8-1:0]  port;
            logic [1-1:0]  discard;

            usr_rx_hdr [index].get(hdr);
            usr_rx_data[index].get(data);

            `uvm_info(this.get_full_name(), $sformatf("\nUSR RX [%0d]\nHEADER%s\nDATA%s\n", index, hdr.convert2string(), data.convert2string()), UVM_FULL);


            if (data.size() >= 64) begin
                {discard, port, length} = hdr.data;
                hdr_out = uvm_logic_vector::sequence_item#(1)::type_id::create("hdr_out", this);
                hdr_out.start[$sformatf("USR_RX[%0d]", index)] = $time();
                hdr_out.tag = "ETH_TX";
                hdr_out.data = 1'b0; 

                data_out = data;
                //data_out = uvm_logic_vector_array::sequence_item#(ITEM_WIDTH)::type_id::create("data_out", this);
                //data_out.start[$sformatf("USR_RX[%0d]", index)] = $time();
                //data_out.tag = "ETH_TX";
                //data_out = data;

                eth_tx_hdr [index].write(hdr_out);
                eth_tx_data[index].write(data_out);
            end
        end
    endtask

    task run_phase(uvm_phase phase);
        for (int unsigned it = 0; it < ETH_PORTS; it++) begin
            fork
                automatic int unsigned index = it;
                run_eth(index);
                run_usr(index);
            join_none
        end
    endtask

    virtual function logic is_frame_valid(logic [6-1 : 0] error_data);
        //0=> malformed packet, 1=> CRC error,  2=> data.size() < 64, 3 => data_size > rx_max_frame_size, 4 => if eth_type <= 1500 then data.size() != eth_type;
        return !(|error_data);
    endfunction

endclass
