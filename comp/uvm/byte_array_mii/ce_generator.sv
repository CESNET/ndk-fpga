/*
 * file       : ce_generator.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: UVM Byte array - MII Clock enable generator
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class ce_gen_config extends uvm_object;

    `uvm_object_utils(uvm_byte_array_mii::ce_gen_config);

    int delta;

    function new(string name = "ce_gen_config");
        super.new(name);

        this.delta = 0;
    endfunction

endclass

class ce_generator_base extends uvm_object;
    `uvm_object_utils(uvm_byte_array_mii::ce_generator_base);

    rand bit clock_enable;
    uvm_byte_array_mii::ce_gen_config ce_gen_config;

    //  Constructor: new
    function new(string name = "ce_gen_base");
        super.new(name);
    endfunction: new

    //  Group: Functions
    virtual function bit get_ce();
        `uvm_fatal(get_name(), "Cannot use base class for clock enable generation!\n")
    endfunction

endclass: ce_generator_base

// Generates CE randomly with maximum difference of total count of log. '1' and log. '0'
class ce_generator_random #(int unsigned MAX_DELTA) extends uvm_byte_array_mii::ce_generator_base;
    `uvm_object_utils(uvm_byte_array_mii::ce_generator_random #(MAX_DELTA));

    //  Constructor: new
    function new(string name = "ce_gen_base");
        super.new(name);
    endfunction: new

    //  Group: Functions
    function bit get_ce();
        this.randomize();
        if (this.clock_enable == 1'b1) begin
            if (this.ce_gen_config.delta + 1 > MAX_DELTA) begin
                this.ce_gen_config.delta--;
                return 1'b0;
            end else begin
                this.ce_gen_config.delta++;
                return this.clock_enable;
            end
        end else if (this.clock_enable == 1'b0) begin
            if (this.ce_gen_config.delta - 1 < -MAX_DELTA) begin
                this.ce_gen_config.delta++;
                return 1'b1;
            end else begin
                this.ce_gen_config.delta--;
                return this.clock_enable;
            end
        end else begin
            `uvm_fatal(get_name(), "Clock enable generator failed!\n")
        end
    endfunction

endclass: ce_generator_random

// Generates alternating clock enable
class ce_generator_alternate extends uvm_byte_array_mii::ce_generator_base;
    `uvm_object_utils(uvm_byte_array_mii::ce_generator_alternate);

    //  Constructor: new
    function new(string name = "ce_gen_base");
        super.new(name);
        this.clock_enable = 1'b0;
    endfunction: new

    //  Group: Functions
    function bit get_ce();
        this.clock_enable = ~this.clock_enable;
        return this.clock_enable;
    endfunction

endclass: ce_generator_alternate

// Generates CE = '1'
class ce_generator_one extends uvm_byte_array_mii::ce_generator_base;
    `uvm_object_utils(uvm_byte_array_mii::ce_generator_one);

    //  Constructor: new
    function new(string name = "ce_gen_base");
        super.new(name);
        this.clock_enable = 1'b1;
    endfunction: new

    //  Group: Functions
    function bit get_ce();
        return this.clock_enable;
    endfunction

endclass: ce_generator_one
