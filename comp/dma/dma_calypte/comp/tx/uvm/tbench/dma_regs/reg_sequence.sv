// reg_sequence: Register sequence
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


class start_channel_seq extends uvm_sequence;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::start_channel_seq)

    regmodel_channel m_regmodel_channel;

    function new (string name = "start_channel_seq");
        super.new(name);
    endfunction

    //set base address, mask, pointers
    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;

        int unsigned start_attempts = 0;

        //Randomize sequence of doing this
        //write sw_pointers
        m_regmodel_channel.sw_data_pointer_reg.write(status, 'h0, .parent(this));
        m_regmodel_channel.sw_hdr_pointer_reg .write(status, 'h0, .parent(this));

        //startup channel
        m_regmodel_channel.control_reg.write(status,  32'h1,  .parent(this));

        do begin
            #(300ns)
            m_regmodel_channel.status_reg.read(status, data, .parent(this));

            assert (start_attempts < 100) else
                `uvm_warning(this.get_type_name(), "\n\nThe start of a channel takes suspiciously long time!\n")

        end while ((data & 32'h1) != 1);
    endtask
endclass

class stop_channel_seq extends uvm_sequence;
    `uvm_object_utils(uvm_tx_dma_calypte_regs::stop_channel_seq)

    regmodel_channel m_regmodel_channel;

    function new (string name = "start_channel_seq");
        super.new(name);
    endfunction

    //set base address, mask, pointers
    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;

        int unsigned sw_data;
        int unsigned hw_data;
        int unsigned sw_hdr;
        int unsigned hw_hdr;

        int unsigned stop_attempts = 0;

        m_regmodel_channel.control_reg.write(status,  32'h0,  .parent(this));

        do begin
            m_regmodel_channel.hw_data_pointer_reg.read (status, data, .parent(this));
            m_regmodel_channel.sw_data_pointer_reg.write(status, data, .parent(this));
            m_regmodel_channel.hw_hdr_pointer_reg .read (status, data, .parent(this));
            m_regmodel_channel.sw_hdr_pointer_reg .write(status, data, .parent(this));

            #(500ns);

            m_regmodel_channel.sw_data_pointer_reg.read(status, data, .parent(this));
            sw_data = data;
            m_regmodel_channel.sw_hdr_pointer_reg .read(status, data, .parent(this));
            sw_hdr = data;
            m_regmodel_channel.hw_data_pointer_reg.read(status, data, .parent(this));
            hw_data = data;
            m_regmodel_channel.hw_hdr_pointer_reg .read(status, data, .parent(this));
            hw_hdr = data;

            m_regmodel_channel.status_reg.read(status, data, .parent(this));
            stop_attempts++;

            assert (stop_attempts < 500) else
                `uvm_warning(this.get_type_name(), "\n\nThe stop of a channel takes suspiciously long time!\n")

        end while (sw_data != hw_data || sw_hdr != hw_hdr || (data & 32'h1) != 0);
    endtask
endclass
