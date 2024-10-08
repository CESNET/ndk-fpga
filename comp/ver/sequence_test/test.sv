//-- test.sv: Tests for sequence.sv
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): TomášBeneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mvb_pkg::*;

module testbench();

    // Test inserting general transaction to sequence
    task insComTr();
	    static tTransMbx mbx = new(1);
        static Sequence seq = new("sequenc 1", -1, mbx);
        Transaction tr;
        seq.addTransaction(tr);

	    $write("Test that insert common transaction: ");
        if(seq.listOfTransactions.size == 1)
	        $write("passed\n");
	    else
            $write("failed\n");
    endtask

    task insTrWData();
        static tTransMbx mbx = new(1);
        static Sequence seq = new("2 mvb transactions", 1,mbx);
        static MvbTransaction #(8) tr1 = new();
        static MvbTransaction #(8) tr2 = new();
        tr1.data = 12;
        tr2.data = {4'hA, 4'b0000};

        seq.addTransaction(tr1);
        seq.addTransaction(tr2);

        $write("Test that insert 2 mvb transaction: ");
        if(seq.listOfTransactions.size == 2) begin;
            $write("passed\n");
            seq.display();
        end else begin;
            $write("failed\n");
        end
    endtask

    task enAndDis();
	    static tTransMbx mbx = new(1);
        static Sequence seq = new("2 mvb transactions", 1,mbx);
        static MvbTransaction #(8) tr1 = new();
        static MvbTransaction #(8) tr2 = new();

        seq.addTransaction(tr1);
        seq.addTransaction(tr2);

        seq.setEnabled();
	    #20;
	    seq.setDisabled();

	    $write("Test that enable, wait and then disable sequence: ");
        if(seq.listOfTransactions.size == 2 && seq.enabled == 0) begin;
            $write("passed\n");
        end else begin;
            $write("failed\n");
        end
	    seq.display();
    endtask

    initial begin
    	insComTr();
    	insTrWData();
	    enAndDis();
    end

endmodule

