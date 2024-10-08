//-- reg_sequence: register sequence
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class reg_sequence#(REG_DEPTH, ADDR_WIDTH, LUT_DEPTH, SW_WIDTH) extends uvm_sequence;
    `uvm_object_param_utils(uvm_lookup_table::reg_sequence#(REG_DEPTH, ADDR_WIDTH, LUT_DEPTH, SW_WIDTH))

    regmodel#(REG_DEPTH, SW_WIDTH) m_regmodel;

    function new (string name = "run_channel");
        super.new(name);
    endfunction

    task body();
        uvm_status_e   status;
        uvm_reg_data_t data;
        uvm_reg_data_t value [ADDR_WIDTH];

        foreach (value[i]) begin
            void'(std::randomize(value[i]));
            if (LUT_DEPTH == 1) begin
                m_regmodel.lut.write(status, i*2, value[i]);
            end
        end

        if (LUT_DEPTH > 1) begin
            m_regmodel.lut.burst_write(status, 0, value);
        end
    endtask
endclass
