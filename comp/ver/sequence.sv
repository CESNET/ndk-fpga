//-- sequence.sv: Sequence of transaction
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

class Sequence #(type TransType = Transaction);

    string name;

    int stream_id;

    tTransMbx transMbx;

    TransType listOfTransactions[$];

    bit enabled;


    function new(string name, int stream_id, tTransMbx transMbx);
        this.name=name;
        this.stream_id = stream_id;
        this.transMbx = transMbx;
        this.enabled=0;
    endfunction

    task addTransaction(TransType transaction);
        this.listOfTransactions.push_back(transaction);
    endtask

    task setEnabled();
        this.enabled = 1;
        fork
            run();
        join_none;
    endtask

    task setDisabled();
        this.enabled = 0;
    endtask

    task run();
        for (int index = 0; index< this.listOfTransactions.size; index++ ) begin
	        if(this.enabled == 1) begin
	            this.listOfTransactions[index].stream_id    = this.stream_id;
            	this.listOfTransactions[index].scenario_id  = -1;
            	this.transMbx.put(this.listOfTransactions[index]);
	        end else begin
		        break;
	        end
        end
        this.enabled = 0;
    endtask

    task display();
        $write("------------------------------------------------------------\n");
        $write("-- %s sequence\n", this.name);
        $write("------------------------------------------------------------\n");
        $write("Size: %d\n", $size(listOfTransactions));
        foreach(listOfTransactions[i])begin
            listOfTransactions[i].display();
        end
        $write("------------------------------------------------------------\n");
    endtask

endclass
