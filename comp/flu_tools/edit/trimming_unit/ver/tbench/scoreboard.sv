/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;
import sv_flu_pkg::*;
import math_pkg::*;

  // --------------------------------------------------------------------------
  // -- Frame Link Driver Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardDriverCbs #(int width = 12) extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;
    bit length[$][width];
    Transaction t[$];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table);
      this.sc_table = sc_table;
    endfunction

    virtual task pre_tx(ref Transaction transaction, string inst);
      FrameLinkUTransaction T;
      FrameLinkUTransaction tr;
      byte unsigned data[];
      bit x[width];
      bit xx;
      int ones;
      int val;
      int zeros;

      if("Driver0" == inst) begin
        T=new;
        $cast(tr,transaction);
        tr.copy(T);
        t.push_back(T);
      end;

      if("DriverL" == inst) begin
        $cast(tr,transaction);
        if(tr.data[0]<10) begin // all ones
          for (int j=0; j < width; j++) begin
            x[j]=1;
          end;
        end
        else if (tr.data[0]>180) begin // all zeros
          for (int j=0; j < width; j++) begin
            x[j]=0;
          end;
        end
        else  // trimm length
          for (int j=0; j < width; j++) begin
            x[j]=tr.data[j/8][j%8];
          end;
        /*if(tr.data[0]>200) xx=1; else xx=0;
        for(int i=0; i<width; i++)
          x[i]=xx;*/
        length.push_back(x);
      end;

      if(t.size() && length.size()) begin
        x=length.pop_front();
        tr=t.pop_front();
        ones=1; zeros=1; val=0;
        for(int i=width-1; i>=0; i--) begin
          if(x[i]==0) ones=0;
          if(x[i]==1) zeros=0;
          val=val*2+x[i];
        end;
        if(zeros)
          sc_table.add(tr);
        else if(!ones) begin
          val+= 8;
          if(val<tr.data.size()) begin
            data = new[val];
            for(int i=0; i<val; i++)
              data[i]=tr.data[i];
            tr.data=data;
          end;
          sc_table.add(tr);
        end;
      end;

      //transaction.display(inst);
    endtask

    // ------------------------------------------------------------------------
    // Function is called after is transaction sended

    virtual task post_tx(Transaction transaction, string inst);
    endtask

   endclass : ScoreboardDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class ScoreboardMonitorCbs #(int width = 12) extends MonitorCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new (TransactionTable #(TR_TABLE_FIRST_ONLY) sc_table);
      this.sc_table = sc_table;
    endfunction

    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)

    virtual task post_rx(Transaction transaction, string inst);
      bit status=0;
      //transaction.display(inst);
      sc_table.remove(transaction, status);
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         transaction.display();
         sc_table.display();
         $stop;
       end
    endtask

  endclass : ScoreboardMonitorCbs

  // -- Constructor ---------------------------------------------------------
  // Create a class
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Scoreboard #(int width = 12);

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable #(TR_TABLE_FIRST_ONLY) scoreTable;
    ScoreboardMonitorCbs #(width) monitorCbs;
    ScoreboardDriverCbs  #(width) driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction

    // -- Display -------------------------------------------------------------
    // Create a class
    task display();
      scoreTable.display(0);
    endtask

  endclass : Scoreboard
