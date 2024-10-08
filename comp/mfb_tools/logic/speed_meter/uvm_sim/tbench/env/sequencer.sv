// sequencer.sv: Virtual sequencer
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


class virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH) extends uvm_sequencer;
    `uvm_component_param_utils(uvm_speed_meter::virt_sequencer#(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, MI_DATA_WIDTH, MI_ADDRESS_WIDTH))

    uvm_reset::sequencer                                                  m_reset_sqr;
    uvm_logic_vector_array::sequencer#(ITEM_WIDTH)                        m_mfb_data_sqr;
    uvm_mi::sequencer_slave#(MI_DATA_WIDTH, MI_ADDRESS_WIDTH)             m_mi_sqr;
    uvm_mfb::sequencer #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0) m_mfb_rdy_sqr;

    function new(string name = "virt_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass
