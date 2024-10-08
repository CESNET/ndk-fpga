/*
 * root.sv
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

class root #(DEVICE, DATA_WIDTH);

    base pcie_root;

    localparam AXI_CQ_TUSER_WIDTH = (DEVICE=="7SERIES") ? 85 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 183 : 88;
    localparam AXI_CC_TUSER_WIDTH = (DEVICE=="7SERIES") ? 33 : (DEVICE=="ULTRASCALE" && DATA_WIDTH == 512) ? 81  : 33;

    function new (string inst, sv_common_pkg::tTransMbx transMbx, virtual i_pcie_c #(DEVICE, DATA_WIDTH) vif);
        ifg_config_rand_setup rx_ifg_rand_cfg = new();
        ifg_config_rand_setup tx_ifg_rand_cfg = new();

        if (DEVICE == "ULTRASCALE" || DEVICE == "7SERIES") begin
            axi #(DATA_WIDTH, AXI_CQ_TUSER_WIDTH, AXI_CC_TUSER_WIDTH) axi_class;

            axi_class = new({inst, " AXI :"}, transMbx, vif.AXI.CQ, vif.AXI.CC);
            pcie_root = axi_class;
        end else if (DEVICE == "STRATIX10") begin
            avalon #(DATA_WIDTH) avalon_class;

            avalon_class = new ({inst, " AVALON :"}, transMbx, vif.AVALON.CQ, vif.AVALON.CC);
            pcie_root = avalon_class;
        end else begin
            $error("UNKNOWN DEVICE %s\n", DEVICE);
            $stop();
        end
    endfunction

    virtual task setEnabled();
        pcie_root.setEnabled();
    endtask

    virtual task setDisabled();
        pcie_root.setEnabled();
    endtask

    virtual function void verbose_set(int unsigned level);
        pcie_root.verbose_set(level);
    endfunction

    virtual function void setPcieCQCallbacks(sv_common_pkg::DriverCbs cbs);
        pcie_root.setPcieCQCallbacks(cbs);
    endfunction

    function void ifg_set(ifg_config_rand_setup rx, ifg_config_rand_setup tx);
        pcie_root.ifg_set(rx, tx);
    endfunction

    virtual function void setPcieCCCallbacks(sv_common_pkg::MonitorCbs cbs);
        pcie_root.setPcieCCCallbacks(cbs);
    endfunction
endclass
