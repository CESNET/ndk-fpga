/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class agent #(REGIONS);

    driver #(REGIONS) m_driver;

    ////////////////////
    // functions
    function new(string inst, sv_common_pkg::tTransMbx mbx, virtual avst_tx_if #(REGIONS) vif, config_item cfg = null);
        m_driver = new(inst, mbx, vif, cfg);
    endfunction

    function void verbosity_set(int unsigned level);
        m_driver.verbosity_set(level);
    endfunction

    task setEnabled();
        m_driver.setEnabled();
    endtask;

    task setDisabled();
        m_driver.setDisabled();
    endtask
endclass

