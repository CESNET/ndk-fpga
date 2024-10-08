/*!
 * \file responder.sv
 * \brief Responder
 * \author Martin Spinler <spinler@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

class Responder;

    string inst;
    bit enabled;

    function new(string i);
        enabled = 0;
        inst = i;
    endfunction

    task setEnabled();
        enabled = 1;
        fork
            run();
        join_none;
    endtask

    task setDisabled();
        enabled = 0;
    endtask

    virtual task run();
        while(enabled) begin
           #1;
        end
    endtask

endclass
