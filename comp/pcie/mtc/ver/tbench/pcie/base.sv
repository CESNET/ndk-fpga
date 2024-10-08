
/*
 * base.sv base class for pcie
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
 * Author(s): Radek Iša <isa@cesnet.cz>
 */

///////////////////////////////////////////////
// base class for converting pcie transaction to AVALON/AXI transaction
///////////////////////////////////////////////
class pcieDataRand;
    rand logic [31:0] data[];
endclass

///////////////////////////////////////////////////
// RANDOMIZATION IFG CONGIG
///////////////////////////////////////////////////
class ifg_config_rand_setup;
    //rand count have to be set to zero
    rand int unsigned rand_count   = 0;
    rand int unsigned ifg_enabled  = 0;
    rand int unsigned ifg_disabled = 1;
    rand int unsigned ifg_low      = 0;
    rand int unsigned ifg_high     = 18;

    int unsigned enable_min = 0;
    int unsigned enable_max = 0;
    int unsigned disable_min = 0;
    int unsigned disable_max = 40;

    constraint c1{
       rand_count inside {[20:100]};
       //delay enabled
       ifg_enabled   inside {[enable_min:enable_max]};
       ifg_disabled  inside {[disable_min:disable_max]};
       (ifg_enabled != 0) || (ifg_disabled != 0);
       //delay long
       ifg_low <= ifg_high;
       ifg_low  dist {[0:10] :/ 40, [20:40] :/ 20, [50:100] :/ 10, [110:160] :/ 5};
       ifg_high dist {[0:10] :/ 40, [20:40] :/ 20, [50:100] :/ 10, [110:160] :/ 5};
    };

    function void display(string prefix = "");
        $write("=================================================\n");
        $write("== %s\n", prefix);
        $write("=================================================\n");
        $write("\trand count   : %d\n", rand_count);
        $write("\tifg_enabled  : %d  - [%4d:%4d]\n", ifg_enabled, enable_min, enable_max);
        $write("\tifg_disabled : %d  - [%4d:%4d]\n", ifg_disabled, disable_min, disable_max);
        $write("\tifg_low      : %d\n", ifg_low);
        $write("\tifg_high     : %d\n", ifg_high);
    endfunction
endclass

class ifg_config;
    rand bit enabled;
    rand int unsigned length;

    int unsigned ifg_enabled  = 0;
    int unsigned ifg_disabled = 1;
    int unsigned ifg_low      = 0;
    int unsigned ifg_high     = 18;

    constraint cDelayBase {
        enabled dist {1'b1 := ifg_enabled, 1'b0 := ifg_disabled};
        length  inside {[ifg_low:ifg_high]};
    }
endclass

///////////////////////////////////////////////////
// PCIE TO COMMON AVALON/AXI
///////////////////////////////////////////////////
class pcie2common #(TAG_WIDTH) extends sv_common_pkg::Driver;
    logic [TAG_WIDTH-1:0] tag = 0;
    ifg_config  ifg;

    function new (string inst, sv_common_pkg::tTransMbx inMbx);
        super.new(inst, inMbx);
        this.ifg = new();
    endfunction

    function ifg_set(ifg_config  ifg);
        this.ifg = ifg;
    endfunction

    task getTr(output PcieRequest tr_in);
        pcieDataRand               rand_data = new();
        sv_common_pkg::Transaction tr;
        Transaction tr_get;
        int data_size;

        transMbx.get(tr);
        foreach (cbs[i]) begin
            cbs[i].pre_tx(tr, inst);
        end
        $cast(tr_get, tr);

        data_size = tr_get.data_size;
        tr_in = new();
        tr_in.addr = tr_get.addr[63:2];
        case (tr_get.addr[1:0] & 2'b11)
            0 : begin tr_in.fbe = 4'b1111; data_size += 0; end
            1 : begin tr_in.fbe = 4'b1110; data_size += 1; end
            2 : begin tr_in.fbe = 4'b1100; data_size += 2; end
            3 : begin tr_in.fbe = 4'b1000; data_size += 3; end
        endcase

        case (data_size & 3)
            1 : begin tr_in.lbe = 4'b0001; data_size += 3; end
            2 : begin tr_in.lbe = 4'b0011; data_size += 2; end
            3 : begin tr_in.lbe = 4'b0111; data_size += 1; end
            0 : begin tr_in.lbe = 4'b1111; data_size += 0; end
        endcase

        if (data_size <= 4) begin
            tr_in.fbe &= tr_in.lbe;
            tr_in.lbe   =  0;
        end

        tr_in.length = data_size/4;
        if (tr_get.rw == 0) begin
            tr_in.type_tr = PCIE_RQ_READ;
            assert(rand_data.randomize() with {data.size() == 0;});
        end else begin
            tr_in.type_tr = PCIE_RQ_WRITE;
            assert(rand_data.randomize() with {data.size() == tr_in.length;});
        end
        tr_in.tag = tag;
        tag++;
        tr_in.data   = rand_data.data;
    endtask
endclass

///////////////////////////////////////////////
// base class for AVALON/AXI agent
///////////////////////////////////////////////
class base;

    string inst;

    function new(string inst);
        this.inst = inst;
    endfunction

    virtual task setEnabled();
    endtask

    virtual task setDisabled();
    endtask

    virtual function void verbose_set(int unsigned level);
    endfunction

    virtual function void setPcieCQCallbacks(sv_common_pkg::DriverCbs cbs);
    endfunction

    virtual function void ifg_set(ifg_config_rand_setup rx, ifg_config_rand_setup tx);
    endfunction

    virtual function void setPcieCCCallbacks(sv_common_pkg::MonitorCbs cbs);
    endfunction
endclass
