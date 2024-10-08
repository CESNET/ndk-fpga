/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class agent #(AVST_REGIONS);

    monitor #(AVST_REGIONS) m_monitor_packet;
    driver  #(AVST_REGIONS) m_driver_packet;

    ////////////////////
    // functions
    function new(string inst, virtual avst_rx_if #(AVST_REGIONS) vif, config_item cfg = null);
        m_monitor_packet = new(inst, vif);
        m_driver_packet  = new(inst, vif, cfg);
    endfunction

    function void ifg_set(ifg_config vld);
        m_driver_packet.ifg_set(vld);
    endfunction

    function void setCallbacks(sv_common_pkg::MonitorCbs cbs);
        m_monitor_packet.setCallbacks(cbs);
    endfunction

    function void verbosity_set(int unsigned level);
        m_monitor_packet.verbosity_set(level);
        m_driver_packet.verbosity_set(level);
    endfunction

    task setEnabled();
        m_monitor_packet.setEnabled();
        m_driver_packet.setEnabled();
    endtask;

    task setDisabled();
        m_monitor_packet.setDisabled();
        m_driver_packet.setDisabled();
    endtask
endclass

