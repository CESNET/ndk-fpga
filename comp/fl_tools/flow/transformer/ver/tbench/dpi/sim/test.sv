/*
 * test.sv: SystemVerilog DPI functions test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */
import dpi_scoreboard_pkg::*;

module testbench();

  initial begin
      tFlTransactionInfo info;
      $display("\n\n");
      $display("-------------------------------------\n");
      $display("SystemVerilog DPI: dpi_scoreboard_pkg\n");
      $display("-------------------------------------\n\n");

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=1;
        info.inst="Driver";
        assert(c_flPostTx(info,0,"1Prvni"));
        assert(c_flPostTx(info,0,"1Druhy"));
        assert(c_flPostTx(info,1,"1Treti"));

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=1;
        info.inst="Monitor";
        assert(c_flPostRx(info,0,"1Prvni"));
        assert(c_flPostRx(info,0,"1Druhy"));
        assert(c_flPostRx(info,1,"1Treti"));

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=2;
        info.inst="Driver";
        assert(c_flPostTx(info,0,"2Prvni"));
        assert(c_flPostTx(info,0,"2Druhy"));
        assert(c_flPostTx(info,1,"2Treti"));

        info.stream_id=0;
        info.scenario_id=0;
        info.data_id=2;
        info.inst="Monitor";
        assert(c_flPostRx(info,0,"2Prvni"));
        assert(c_flPostRx(info,0,"2Druhy"));
        assert(c_flPostRx(info,1,"2Treti"));

        c_display();
  end
endmodule

