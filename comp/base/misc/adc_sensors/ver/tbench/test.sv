//  test.sv
//  Copyright (C) 2019 CESNET z. s. p. o.
//  Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
//
//  SPDX-License-Identifier: BSD-3-Clause

import sv_common_pkg::*;
import sv_mi32_pkg::*;
import test_pkg::*;

program TEST (
    input  logic  CLK,
    output logic  RESET,
    iMi32.tb      MI
);

    Mi32Transaction mi32Transaction = new();
    Mi32Driver      mi32Driver      = new("Mi32 Driver", null, MI);
    Mi32Monitor     mi32Monitor     = new("Mi32 Monitor", MI);

    ///////////////////////// EXPECTED VALUES //////////////////////////////////////////////////////

    // Status register, used for checking which values have been read
    logic [31:0] stat_reg;
    // Registers for CONF and CTRL
    logic [31:0] controls[0:1] = {32'hFFFF01FF, 32'h00000000};
    // Addresses for temperatures
    static logic [31:0] temp_addr [0:8] = {32'h10, 32'h14, 32'h18, 31'h1C,
                                           32'h20, 32'h24, 32'h28, 32'h2C,
                                           32'h30};
    // Addresses for voltages
    static logic [31:0] volt_addr [16:31] = {32'h40, 32'h44, 32'h48, 32'h4C,
                                             32'h50, 32'h54, 32'h58, 32'h5C,
                                             32'h60, 32'h64, 32'h68, 32'h6C,
                                             32'h70, 32'h74, 32'h78, 32'h7C};
    // Temperatures from temp0 to temp8
    static logic [31:0] temps [0:8]  = {32'h00FF0001, 32'h00FF0002, 32'h00FF0004, 32'h00FF0008,
                                        32'h00FF0010, 32'h00FF0020, 32'h00FF0040, 32'h00FF0080,
                                        32'h00FF0100};
    // Voltages from volt0 to volt15
    static logic [31:0] volts [16:31] = {32'hFF000001, 32'hFF000002, 32'hFF000004, 32'hFF000008,
                                         32'hFF000010, 32'hFF000020, 32'hFF000040, 32'hFF000080,
                                         32'hFF000100, 32'hFF000200, 32'hFF000400, 32'hFF000800,
                                         32'hFF001000, 32'hFF002000, 32'hFF004000, 32'hFF008000};

    //////////////// HELPER TASKS /////////////////////////////////////////////////////////////

    // Used for initial reset
    task resetDesign();
        RESET=1;
        #RESET_TIME RESET = 0;
    endtask

    // Used for setting the control register based on the
    // configuration inside test_pkg.
    task test_setup();
        if (TEST_TEMP == 0 && TEST_VOLT == 0) begin
            $write("\n\n NOTHING TO TEST, STOPPING! \n\n");
            $stop();
        end else begin
            if (TEST_TEMP == 1) begin
                controls[1][0] = 1;
            end;
            if (TEST_VOLT == 1) begin
                controls[1][16] = 1;
            end;
        end;
    endtask

    // Used for writing data to a register
    task reg_write(input logic[31:0] addr, input logic[31:0] data_in, input logic[3:0] BE);
        // Setup
        mi32Transaction.rw = 1;
        mi32Transaction.address = addr;
        mi32Transaction.data = data_in;
        mi32Transaction.be = BE;
        // Execution
        mi32Driver.sendTransaction(mi32Transaction);
        mi32Transaction.display();
    endtask

    // Used for reading data from a register
    task reg_read(input logic[31:0] addr);
        // Setup
        mi32Transaction.rw = 0;
        mi32Transaction.address = addr;
        mi32Transaction.data = 32'h00000000;
        mi32Transaction.be = 4'hF;
        // Execution
        mi32Monitor.executeTransaction(mi32Transaction);
        mi32Transaction.display();
    endtask

    // Used for reading data from a register, and outputing the result to data vector
    task reg_read_do(input logic[31:0] addr, output logic[31:0] data);
        // Setup
        mi32Transaction.rw = 0;
        mi32Transaction.address = addr;
        mi32Transaction.data = 32'h00000000;
        mi32Transaction.be = 4'hF;
        // Execution
        mi32Monitor.executeTransaction(mi32Transaction);
        // Output
        data = mi32Transaction.data;
    endtask

    // Used for writing a fail message to stdout
    task fail_message(input logic[31:0] expected_data);
        $write("\n\n======================= FAIL ====================\n");
        mi32Transaction.display();
        $write("Expected value: %h\n", expected_data);
        $write("=================================================\n\n\n");
        $stop;
    endtask

    // Used for waiting until all required temp values are read
    task wait_for_t(input logic[15:0] expected_data);
        do begin
            reg_read_do(32'h8, stat_reg);
        end
        while (stat_reg[15:0] !== expected_data);
    endtask

    // Used for waiting until all required volt values are read
    task wait_for_v(input logic[15:0] expected_data);
        do begin
            reg_read_do(32'h8, stat_reg);
        end
        while (stat_reg[31:16] !== expected_data);
    endtask

    // Used for checking values once they have been read by sensor_interface
    // from the IP Core. The function loops over all values, and if the received
    // value differs from the expected value, it calls the fail_message task.
    task check_vals();
        $write("----------------------TEMPS----------------------\n");
        if (TEST_TEMP == 1) begin
            for (int i = 0; i <= 15; i++) begin
                if (stat_reg[i] == 1) begin
                    reg_read(temp_addr[i]);
                    if (mi32Transaction.data !== temps[i]) begin
                        fail_message(temps[i]);
                    end;
                end;
            end;
        end;
        $write("----------------------VOLTS----------------------\n");
        if (TEST_VOLT == 1) begin
            for (int i = 16; i <= 31; i++) begin
                if (stat_reg[i] == 1) begin
                    reg_read(volt_addr[i]);
                    if (mi32Transaction.data !== volts[i]) begin
                        fail_message(volts[i]);
                    end;
                end;
            end;
        end;
    endtask

    ////////////////////// STANDARD TEST ////////////////////////////////////////////////////////////////
    task test_std();

        $write("\n\n###################### TEST STD #####################\n\n");

        // Setting the CONF register to sample everything.
        reg_write(32'h0, controls[0], 4'hF);
        reg_write(32'h4, controls[1], 4'hF); // ctrl

        // Wait until the STAT register tells us all the expected
        // values have been read.
        $write("Waiting until all values are recorded...\n\n");
        if (TEST_TEMP == 1) begin
            wait_for_t(controls[0][15:0]);
        end;
        if (TEST_VOLT == 1) begin
            wait_for_v(controls[0][31:16]);
        end;

        // Check values
        check_vals();

    endtask

    ////////////////////// BE TEST /////////////////////////////////////////////////////////////////////
    task test_be();

        $write("\n##################### TEST BE #####################\n\n");

        // Setup and check for BE test
        reg_write(32'h0, 32'hFFFFFFFF, 4'hF);
        reg_read(32'h0);

        if (mi32Transaction.data !== 32'hFFFFFFFF) begin
            fail_message(32'hFFFFFFFF);
        end;

        // BE test
        reg_write(32'h0, 32'h0, 4'h3);
        reg_read(32'h0);

        if (mi32Transaction.data !== 32'hFFFF0000) begin
            fail_message(32'hFFFF0000);
        end;

    endtask

    ////////////////////// RECONF TEST /////////////////////////////////////////////////////////////////
    task test_reconf();

        $write("\n################### RECONF TEST ###################\n\n");
        $write("-------------------FIRST CONFIG------------------\n");

        // Setting conf register for temperatures 0,1,3,7
        // and voltages 0,1,3,7,9,11,12,14.
        reg_write(32'h0, 32'h5A8B008B, 4'hF);
        reg_write(32'h4, controls[1], 4'hF); // ctrl

        // Wait until the STAT register tells us all the expected
        // values have been read.
        $write("\nWaiting until all values are recorded...\n\n");
        if (TEST_TEMP == 1) begin
            wait_for_t(32'h008B);
        end;
        if (TEST_VOLT == 1) begin
            wait_for_v(32'h5A8B);
        end;

        check_vals();

        $write("\n------------------SECOND CONFIG------------------\n");

        // Setting onf register for temperatures 2,4,5,6,8
        // and voltages 2,4,5,6,8,10,13,15.
        reg_write(32'h4, 32'h0, 4'hF);
        reg_write(32'h0, 32'hA5740174, 4'hF);

        // CTRL
        if (TEST_TEMP == 1) begin
            reg_write(32'h4, controls[1], 4'h1);
        end;
        if (TEST_VOLT == 1) begin
            reg_write(32'h4, controls[1], 4'h4);
        end;

        // Wait until the STAT register tells us all the expected
        // values have been read.
        $write("\nWaiting until all values are recorded...\n\n");
        if (TEST_TEMP == 1) begin
            wait_for_t(32'h174);
        end;
        if (TEST_VOLT == 1) begin
            wait_for_v(32'hA574);
        end;

        check_vals();

    endtask

    /////////////////// MAIN //////////////////////////////////////////////////////

    initial begin
        test_setup();
        if (TEST_STD == 1) begin
            resetDesign();
            test_std();
        end;
        if (TEST_BE == 1) begin
            resetDesign();
            test_be();
        end;
        if (TEST_RECONF == 1) begin
            resetDesign();
            test_reconf();
        end;
        $write("\n###################################################\n");
        $write("        VERIFICATION FINISHED SUCCESSFULLY");
        $write("\n###################################################\n\n");
        $stop();
    end

endprogram
