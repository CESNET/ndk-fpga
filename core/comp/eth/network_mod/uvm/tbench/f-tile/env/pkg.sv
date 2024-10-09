// pkg.sv: Package for Intel F-Tile environment
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef NETWORK_MOD_F_TILE_ENV_SV
`define NETWORK_MOD_F_TILE_ENV_SV

package uvm_network_mod_f_tile_env;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter int unsigned SEGMENTS = ((test::ETH_PORT_SPEED[0] == 400) ? 16 :
                                       (test::ETH_PORT_SPEED[0] == 200) ? 8  :
                                       (test::ETH_PORT_SPEED[0] == 100) ? 4  :
                                       (test::ETH_PORT_SPEED[0] == 50 ) ? 2  :
                                       (test::ETH_PORT_SPEED[0] == 40 ) ? 2  :
                                       (test::ETH_PORT_SPEED[0] == 25 ) ? 1  :
                                       (test::ETH_PORT_SPEED[0] == 10 ) ? 1  :
                                                                          0  );

    `include "sequencer_port.sv"
    `include "sequence.sv"
    `include "model.sv"
    `include "tx_error_trimmer.sv"
    `include "env.sv"

endpackage

`endif
