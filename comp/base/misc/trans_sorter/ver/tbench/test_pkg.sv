//-- test_pkg.sv: Test Package.
//-- Copyright (C) 2020 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    // -- FREQUENTLY CHANGED PARAMETERS ---------------------------------------
    parameter TRANSACTION_COUNT = 5000;
    parameter VERBOSE_LEVEL     = 0;

    // -- DUT PARAMETERS ------------------------------------------------------
    parameter ID_WIDTH      = 8;
    parameter META_WIDTH    = 1;

    parameter BEHAVIOUR     = 0;
    parameter MAX_SAME_ID   = 1;

    parameter FIFOX_SHAKEDOWN_MODE = 0;

    parameter MAX_RX_TRANS  = 2;
    parameter MAX_TX_TRANS  = 2;
    parameter MAX_ID_CONFS  = 2;

    parameter ALMOST_FULL_OFFSET=MAX_RX_TRANS+1;

    // -- LIMIT VALUES FOR GENERATION -----------------------------------------
    parameter DELAY_BETWEEN_CONFS_HIGH  = 10;
    parameter DELAY_BETWEEN_CONFS_LOW   = 1;
    parameter NUMBER_OF_TRANS_HIGH      = (2**ID_WIDTH)/2;
    parameter NUMBER_OF_TRANS_LOW       = 0;
    parameter DELAY_TO_SEND_CONFS_HIGH  = 10;
    parameter DELAY_TO_SEND_CONFS_LOW   = 1;

    // -- CLOCKS AND RESETS ---------------------------------------------------
    parameter CLK_PERIOD    = 10ns;
    parameter RESET_TIME    = 10*CLK_PERIOD;

    // -- CONSTANT VERIFICATION PARAMETERS ------------------------------------
    parameter ITEM_WIDTH                            = ID_WIDTH + META_WIDTH;
    parameter TIME_TO_WAIT_AFTER_GENERATOR_FINISHED = TRANSACTION_COUNT*ID_WIDTH;


    `include "scoreboard.sv"

endpackage
