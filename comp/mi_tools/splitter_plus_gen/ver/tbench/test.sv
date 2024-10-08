/*!
 * \file test.sv
 * \brief Test
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;
import sv_mi_pkg::*;
import sv_common_pkg::*;

program TEST (
    input logic   CLK,
    output logic  RESET,
    iMi           MI_MASTER,
    iMi           MI_SLAVE[PORTS]
);

    virtual iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) V_MI_SLAVE[PORTS] = MI_SLAVE;
    sequence_pkg::mi_sequence #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) rx_blueprint;
    MiTransaction #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tx_blueprint;
    Generator rx_generator;
    Generator tx_generator;
    MiAgentMaster #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) rx_agent;
    MiAgentSlave #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) tx_agent[PORTS];
    string tx_agent_name;
    Scoreboard #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH, PORTS, ADDR_MASK, ADDR_BASES, ADDR_BASE, PORT_MAPPING) sc;

    task setBlueprint();

        rx_blueprint = new;
        rx_generator.blueprint = rx_blueprint;

        tx_blueprint = new;
        tx_generator.blueprint = tx_blueprint;
    endtask

    task createEnvironment();

        rx_generator = new("Generator", 0);
        tx_generator = new("Generator", 0);

        sc = new();
        rx_agent = new("RX agent", rx_generator.transMbx, MI_MASTER);
        rx_agent.monitor.setCallbacks(sc.rxCbs);

        for (int i = 0; i < PORTS; i++) begin
            sequence_pkg::rand_mi_responder_delay slave_rand_ardy;
            sequence_pkg::rand_mi_responder_delay slave_rand_drdy;

            slave_rand_ardy = new();
            slave_rand_drdy = new();
            tx_agent_name = {"TX agent ", $sformatf("%0d",i)};
            tx_agent[i] = new(tx_agent_name, tx_generator.transMbx, V_MI_SLAVE[i]);
            tx_agent[i].responder.rand_ardy = slave_rand_ardy;
            tx_agent[i].responder.rand_drdy = slave_rand_drdy;
            tx_agent[i].monitor.setCallbacks(sc.txCbs[i]);
        end

    endtask

    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    task enableTestEnvironment();
        sc.setEnable();
        for (int i = 0; i < PORTS; i++) begin
            tx_agent[i].setEnabled();
        end
        rx_agent.setEnabled();
    endtask

    task disableTestEnvironment();
        rx_generator.setDisabled();
        fork
            //be carefull. you cannot disabled tx generator when RX is not running
            tx_generator.setDisabled();
        join_none;

        rx_agent.setDisabled();
        for (int i = 0; i < PORTS; i++) begin
            tx_agent[i].setDisabled();
        end
        sc.setDisable();
    endtask

    task test1();
        $write("\n\n############ TEST CASE 1 ############\n\n");
        setBlueprint();
        enableTestEnvironment();
        resetDesign();
        tx_generator.setEnabled();
        rx_generator.setEnabled(TRANSACTION_COUNT);
        wait(!rx_generator.enabled);
        disableTestEnvironment();
    endtask

    initial begin
        createEnvironment();
        test1();
        $write("Verification finished successfully!\n");
        $stop();
    end

endprogram
