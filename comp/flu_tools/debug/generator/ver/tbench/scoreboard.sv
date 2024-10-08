/*
 * scoreboard.sv: Basic scoreboard implementation
 * Copyright (C) 2018 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;



class ScoreboardMonitorCbs extends MonitorCbs;
  int expected_length;
  int cnt;

  virtual task post_rx(Transaction transaction, string inst);
    FrameLinkUTransaction ft;
    $cast(ft, transaction);
    cnt = cnt + 1;
    if(expected_length != ft.data.size) begin
      $write("ERROR: Transaction #%0d with length %0dB captured!\n", cnt, ft.data.size);
      //$stop();
    end
  endtask
endclass


class Scoreboard;
  ScoreboardMonitorCbs monitorCbs;

  function new ();
    this.monitorCbs = new;
  endfunction

  task init(int length);
    monitorCbs.expected_length = length;
    monitorCbs.cnt = 0;
  endtask

  task display();
    $write("%0d transactions passed\n", monitorCbs.cnt);
  endtask
endclass
