/*
 * file       : reg_seq.sv
 * description: Register sequences for MAC Lites
 * date       : 2022
 * author     : Daniel Kondys <xkondy00@vutbr.cz>
 *
 * Copyright (C) 2022 CESNET z. s. p. o.
*/

class sequence_simple #(ETH_CHANNELS) extends uvm_sequence;
    `uvm_object_param_utils(net_mod_logic_env::sequence_simple#(ETH_CHANNELS))
    mac_reg#(ETH_CHANNELS) regmodel;

    function new (string name = "sequence_simple");
        super.new(name);
    endfunction

    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;
        for (int i = 0; i < ETH_CHANNELS; i++) begin
            regmodel.tx_mac_reg[i].write(status, 1'b1, .parent(this)); // enable TX MAC Lites
            regmodel.rx_mac_reg[i].write(status, 1'b1, .parent(this)); // enable RX MAC Lites
            #(100);
        end
    endtask
endclass