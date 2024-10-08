/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

//////////////////////////////////////////////////
// PCIE_AGENT
// ADDR_WIDTH => ADDRES WIDTH IN PC, COMMON 64
// RCB        => PCIE RCB 64, 128.   COMMON 128
// MPS        => PCIE MAX PAYLOAD SIZE. COMMON 256
// DEVICE     => "STRATIX10", "AGILEX", "ULTRASCALE", "7SERIES"
// DATA_WIDTH => PCIE DATA_WIDTH (DEVICE, DATA_WIDTH) => (STRATIX10, 512), (ULTRASCALE, 512), (7SERIES, 256)
class pcie_agent #(RCB, MPS, DEVICE, DATA_WIDTH);

    agent #(RCB, MPS) agent_base;

    function new (string inst, sv_common_pkg::tTransMbx mbx_input, virtual ipcie_rq #(DEVICE, DATA_WIDTH) vif_rx, virtual ipcie_rc#(DEVICE, DATA_WIDTH).monitor vif_tx);
        if (DEVICE == "STRATIX10" || DEVICE == "AGILEX") begin
            avalon_agent #(RCB, MPS, DEVICE, DATA_WIDTH) avalon;
            avalon = new({inst, " AVALON : "}, mbx_input, vif_rx.AVALON.INF, vif_tx.AVALON.INF);
            agent_base = avalon;
        end else if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin
            sv_pcie_pkg::axi_agent #(RCB, MPS, DEVICE, DATA_WIDTH) axi;
            axi = new({inst, " AXI : "}, mbx_input, vif_rx.AXI.INF, vif_tx.AXI.INF);
            agent_base = axi;
        end else begin
            $error("ERROR %s: UNKNOWN DEVICE : %s\n",inst, DEVICE);
            $stop();
        end
    endfunction

    task setEnabled();
        agent_base.setEnabled();
    endtask

    task setDisabled();
        agent_base.setDisabled();
    endtask

    function void verbosity_set(int unsigned level);
        agent_base.verbosity_set(level);
    endfunction

    function void rq_setCallbacks(sv_common_pkg::MonitorCbs cbs);
        agent_base.rq_setCallbacks(cbs);
    endfunction

    function void rq_ifg_set(ifg_config_setup cfg);
        agent_base.rq_ifg_set(cfg);
    endfunction

    function void rc_ifg_set(ifg_config_setup cfg);
        agent_base.rc_ifg_set(cfg);
    endfunction
endclass


