/*
 * file       : sequence.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: LII sequence
 * date       : 2021
 * author     : Daniel Kriz <xkrizd01@vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class sequence_lib #(int unsigned DATA_WIDTH, logic FAST_SOF, logic DIC_EN, int unsigned VERBOSITY, int unsigned META_WIDTH, int unsigned LOGIC_WIDTH, int unsigned SOF_WIDTH) extends uvm_sequence_library #(uvm_lii::sequence_item #(DATA_WIDTH, META_WIDTH, SOF_WIDTH));
    `uvm_object_param_utils(uvm_byte_array_lii::sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH))
    `uvm_sequence_library_utils(uvm_byte_array_lii::sequence_lib #(DATA_WIDTH, FAST_SOF, DIC_EN, VERBOSITY, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH))
    function new(string name = "");
        super.new(name);
        init_sequence_library();
    endfunction
    virtual function void init_sequence_rx_mac();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_random_link_status #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_random_errors #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_error_with_random_link_status #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_sof_after_eof #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_random_sof #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
    endfunction

    virtual function void init_sequence_mac_rdy();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_tx_random_rdy #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::get_type());
    endfunction

    virtual function void init_sequence_pcs_rdy();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_tx_random_rdy #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_not_rdy_once_for_32_ticks_tx #(DATA_WIDTH, META_WIDTH, SOF_WIDTH)::get_type());
    endfunction

    virtual function void init_sequence_tx_mac();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_tx_mac #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
    endfunction

    virtual function void init_sequence_pcs();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_rx_random_sof #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
    endfunction

    virtual function void init_sequence_eth_phy();
        this.add_sequence(uvm_byte_array_lii::sequence_simple_eth_phy_err_crc #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_eth_phy #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_eth_phy_const_gaps #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
        this.add_sequence(uvm_byte_array_lii::sequence_simple_eth_phy_no_gaps #(DATA_WIDTH, FAST_SOF, META_WIDTH, LOGIC_WIDTH, SOF_WIDTH)::get_type());
    endfunction

endclass
