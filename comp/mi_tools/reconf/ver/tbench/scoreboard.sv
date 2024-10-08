//-- sv_mi_scoreboard_pkg.sv: Scoreboard for common mi fifo verification
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
//--
//-- SPDX-License-Identifier: BSD-3-Clause

// ----------------------------------------------------------------------------
//                        Scoreboard
// ----------------------------------------------------------------------------

class master_cbs #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH, TX_DATA_WIDTH = RX_DATA_WIDTH, TX_ADDR_WIDTH = RX_ADDR_WIDTH, TX_META_WIDTH = RX_META_WIDTH) extends sv_common_pkg::MonitorCbs;

    sv_mi_pkg::MiTransaction #(TX_DATA_WIDTH, TX_ADDR_WIDTH, TX_META_WIDTH) rxtx_req_fifo[$];
    sv_mi_pkg::MiTransaction #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH) rx_res_fifo[$];

    function new ();
        this.rxtx_req_fifo = {};
        this.rx_res_fifo   = {};
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        sv_mi_pkg::MiTransaction #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH) rx_tr;
        sv_mi_pkg::MiTransaction #(TX_DATA_WIDTH, TX_ADDR_WIDTH, TX_META_WIDTH) tx_tr;
        sv_mi_pkg::MiTransaction #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH) rx_tr_ref;
        int word_shift;
        int error = 0;
        string error_str = "";
        $timeformat(-9, 3, " ns", 8);

        $cast(rx_tr,transaction);

        if (VERBOSITY > 0) begin
            $write("New MI Transaction on Master interface!\n");

            $write("Time: %t\n", $time);
            rx_tr.display("Received transaction");
        end

        if (rx_tr.tr_type == sv_mi_pkg::TR_REQUEST) begin

            // Send the request to TX as a reference
            if (RX_DATA_WIDTH < TX_DATA_WIDTH) begin

                // Widen
                tx_tr = new();
                tx_tr.meta    = rx_tr.meta;
                tx_tr.tr_type = rx_tr.tr_type;
                tx_tr.op      = rx_tr.op;

                word_shift = (rx_tr.address % (TX_DATA_WIDTH / 8));

                tx_tr.address = rx_tr.address - word_shift;

                tx_tr.be   = 0;
                tx_tr.data = 0;

                tx_tr.be  [word_shift   +: RX_DATA_WIDTH/8] = rx_tr.be  [0 +: RX_DATA_WIDTH/8];
                tx_tr.data[word_shift*8 +: RX_DATA_WIDTH  ] = rx_tr.data[0 +: RX_DATA_WIDTH  ];

                rxtx_req_fifo.push_back(tx_tr);

            end else if (RX_DATA_WIDTH > TX_DATA_WIDTH) begin

                // Separate
                for (int i = 0; i < RX_DATA_WIDTH / TX_DATA_WIDTH; i++) begin
                    tx_tr = new();
                    tx_tr.meta    = rx_tr.meta;
                    tx_tr.tr_type = rx_tr.tr_type;
                    tx_tr.op      = rx_tr.op;

                    tx_tr.address = rx_tr.address + i;

                    tx_tr.be   = rx_tr.be  [i*TX_DATA_WIDTH/8 +: TX_DATA_WIDTH/8];
                    tx_tr.data = rx_tr.data[i*TX_DATA_WIDTH   +: TX_DATA_WIDTH  ];

                    // Only propagate when at least some BE is valid
                    if (tx_tr.be != 0)
                        rxtx_req_fifo.push_back(tx_tr);

                end

            end else begin

                // No change
                $cast(tx_tr,rx_tr);
                rxtx_req_fifo.push_back(tx_tr);

            end

            if (rx_tr.op == sv_mi_pkg::OP_READ) begin

                // Generate referential response
                $cast(rx_tr_ref,rx_tr.copy());
                rx_tr_ref.tr_type = sv_mi_pkg::TR_RESPONSE;

                rx_res_fifo.push_back(rx_tr_ref);

            end

        end else begin // response

            // Compare response to reference
            if (rx_res_fifo.size() == 0) begin
                error = 1;
                error_str = "Referential FIFO is empty!";
            end else begin

                rx_tr_ref  = rx_res_fifo.pop_front();

                rx_tr.meta    = rx_tr_ref.meta;
                rx_tr.address = rx_tr_ref.address;
                rx_tr.be      = rx_tr_ref.be;

                if (!rx_tr_ref.compare(rx_tr,error_str))
                    error = 2;

            end

            if (error) begin
                $error("Unexpected read response on Master interface! %s\n",error_str);
                $write("Time: %t\n", $time);
                rx_tr.display("Received transaction");

                if (error == 2) begin
                    $write("Referencial transactions FIFO:\n");
                    rx_tr_ref.display();
                    while (rx_res_fifo.size())
                        rx_res_fifo.pop_front().display();
                end
                $stop();
            end;

        end

    endtask

endclass

class slave_cbs #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH, TX_DATA_WIDTH = RX_DATA_WIDTH, TX_ADDR_WIDTH = RX_ADDR_WIDTH, TX_META_WIDTH = RX_META_WIDTH) extends sv_common_pkg::MonitorCbs;

    master_cbs #(RX_DATA_WIDTH,RX_ADDR_WIDTH,RX_META_WIDTH,TX_DATA_WIDTH,TX_ADDR_WIDTH,TX_META_WIDTH) master;

    sv_mi_pkg::MiTransaction #(TX_DATA_WIDTH, TX_ADDR_WIDTH, TX_META_WIDTH) rxtx_req_fifo[$];
    sv_common_pkg::tTransMbx res_mbx;

    function new (master_cbs #(RX_DATA_WIDTH,RX_ADDR_WIDTH,RX_META_WIDTH,TX_DATA_WIDTH,TX_ADDR_WIDTH,TX_META_WIDTH) master,
                  sv_common_pkg::tTransMbx res_mbx
                  );
        this.master  = master;
        this.res_mbx = res_mbx;
    endfunction

    virtual task post_rx(sv_common_pkg::Transaction transaction, string inst);
        // The actual work must be done 0.5 CLK cycles later to make sure that the Master interface
        // callback has time to react first on an asynch event
        fork post_rx_delayed(transaction, inst);
        join_none;
    endtask

    task post_rx_delayed(sv_common_pkg::Transaction transaction, string inst);
        sv_mi_pkg::MiTransaction #(TX_DATA_WIDTH, TX_ADDR_WIDTH, TX_META_WIDTH) tx_tr;
        sv_mi_pkg::MiTransaction #(TX_DATA_WIDTH, TX_ADDR_WIDTH, TX_META_WIDTH) tx_tr_ref;
        int error = 0;
        string error_str = "";
        $timeformat(-9, 3, " ns", 8);

        #(CLK_PERIOD / 2);

        $cast(tx_tr,transaction);

        if (VERBOSITY > 0) begin
            $write("New MI Transaction on Slave interface!\n");

            $write("Time: %t\n", $time);
            tx_tr.display("Received transaction");
        end

        if (tx_tr.tr_type == sv_mi_pkg::TR_REQUEST) begin

            // Compare request to reference
            if (master.rxtx_req_fifo.size() == 0) begin
                error = 1;
                error_str = "Referential FIFO is empty!";
            end else begin

                tx_tr_ref  = master.rxtx_req_fifo.pop_front();

                if (!tx_tr_ref.compare(tx_tr,error_str))
                    error = 2;

            end

            if (error) begin
                $error("Unexpected request on Slave interface! %s\n",error_str);

                $write("Time: %t\n", $time);
                tx_tr.display("Received transaction");

                if (error == 2) begin
                    $write("Referencial transactions FIFO:\n");
                    tx_tr_ref.display();
                    while (master.rxtx_req_fifo.size())
                        master.rxtx_req_fifo.pop_front().display();
                end
                $stop();
            end;

            if (tx_tr.op == sv_mi_pkg::OP_READ) begin

                // Generate response and send it to responder
                tx_tr.tr_type = sv_mi_pkg::TR_RESPONSE;
                res_mbx.put(tx_tr);

            end

        end

    endtask

endclass

class scoreboard #(RX_DATA_WIDTH, RX_ADDR_WIDTH, RX_META_WIDTH, TX_DATA_WIDTH = RX_DATA_WIDTH, TX_ADDR_WIDTH = RX_ADDR_WIDTH, TX_META_WIDTH = RX_META_WIDTH);

    master_cbs #(RX_DATA_WIDTH,RX_ADDR_WIDTH,RX_META_WIDTH,TX_DATA_WIDTH,TX_ADDR_WIDTH,TX_META_WIDTH) master;
    slave_cbs  #(RX_DATA_WIDTH,RX_ADDR_WIDTH,RX_META_WIDTH,TX_DATA_WIDTH,TX_ADDR_WIDTH,TX_META_WIDTH) slave;

    sv_common_pkg::tTransMbx res_mbx;

    function new();
        res_mbx       = new(0);
        master        = new();
        slave         = new(master,res_mbx);
    endfunction

    function void display(string prefix = "");
    endfunction

endclass
