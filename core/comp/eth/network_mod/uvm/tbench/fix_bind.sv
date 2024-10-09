// fix_bind.sv: Module for binding probes on ETH ports
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz>
//            Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

// It only supports single channel combinations with 1, 2 or 4 ports
module fix_bind #(int unsigned PORTS, int unsigned CHANNELS);

    initial begin
        assert(CHANNELS == 1)
        else begin
            $error("%m UNSUPORTED COMBINATION: CHANNELS(%0d)!!!\n", CHANNELS);
        end
    end

    if (PORTS == 1) begin
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[0].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
    end
    else if (PORTS == 2) begin
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[0].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[1].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
    end
    else if (PORTS == 4) begin
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[0].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[1].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[2].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
        bind RX_MAC_LITE_BUFFER : $root.testbench.DUT_U.DUT_BASE_U.VHDL_DUT_U.eth_core_g[3].network_mod_logic_i.rx_g[0].rx_mac_g.rx_mac_i.buffer_i
                probe_inf #(2*REGIONS) probe_drop(s_rx_src_rdy_orig_reg, {s_rx_eof_orig_reg, s_rx_force_drop_reg}, RX_CLK);
    end
    else begin
        $error("%m UNSUPORTED COMBINATION: PORTS(%0d)!!!\n", PORTS);
    end

endmodule
