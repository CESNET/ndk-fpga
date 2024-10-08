// meter.sv: measure pcie statistic
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Radek Iša <isa@cesnet.cz> 

// SPDX-License-Identifier: BSD-3-Clause 



`uvm_analysis_imp_decl(_rq)
`uvm_analysis_imp_decl(_rc)
`uvm_analysis_imp_decl(_cq)
`uvm_analysis_imp_decl(_cc)


// Definition of mfb monitor
class stats  extends uvm_component;
    `uvm_component_utils(uvm_pcie::stats)

    localparam KOEF = 32;

    typedef uvm_pcie::stats this_type;
    uvm_analysis_imp_rq#(uvm_pcie::request_header  , this_type) rq_analysis_export;
    uvm_analysis_imp_rc#(uvm_pcie::completer_header, this_type) rc_analysis_export;
    uvm_analysis_imp_cq#(uvm_pcie::request_header  , this_type) cq_analysis_export;
    uvm_analysis_imp_cc#(uvm_pcie::completer_header, this_type) cc_analysis_export;


    // ------------------------------------------------------------------------
    // Parameters
    //int unsigned error_speed; //In items
    protected int unsigned       rq_packets;
    protected int unsigned       rc_packets;
    protected int unsigned       cq_packets;
    protected int unsigned       cc_packets;
    protected uvm_common::stats  rq_speed;
    protected uvm_common::stats  rq_data_size;
    protected time               rq_last_update;
    protected uvm_common::stats  rc_speed;
    protected uvm_common::stats  rc_data_size;
    protected time               rc_last_update;
    protected uvm_common::stats  cq_speed;
    protected uvm_common::stats  cq_data_size;
    protected time               cq_last_update;
    protected uvm_common::stats  cc_speed;
    protected uvm_common::stats  cc_data_size;
    protected time               cc_last_update;

    protected int unsigned       sections;
    protected time               section_time;

    // ------------------------------------------------------------------------
    // Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        rq_speed       = new();
        rq_data_size   = new();
        rc_speed         = new();
        rc_data_size     = new();
        cq_speed       = new();
        cq_data_size   = new();
        cc_speed         = new();
        cc_data_size     = new();

        rq_analysis_export = new("rq_analysis_export", this);
        rc_analysis_export = new("rc_analysis_export", this);
        cq_analysis_export = new("cq_analysis_export", this);
        cc_analysis_export = new("cc_analysis_export", this);

        section_time = 500us;
    endfunction

    // ------------------------------------------------------------------------
    // Functions
    virtual function void write_rq(uvm_pcie::request_header t);
        int unsigned data_size;
        const time update_time_new = $time();
        int unsigned divider;
        rq_packets += 1;

        data_size = t.data.size() + (t.fmt[0] == 1 ? 4 : 3);
        rq_data_size.next_val(data_size);
        divider = (update_time_new - rq_last_update)/1ns;
        divider = (divider != 0) ? divider : 1;
        rq_speed.next_val(real'(data_size)/divider);
        rq_last_update = update_time_new;
    endfunction

    virtual function void write_rc(uvm_pcie::completer_header t);
        int unsigned data_size;
        const time update_time_new = $time();
        int unsigned divider;
        rc_packets += 1;

        data_size = t.data.size() + 3;
        rc_data_size.next_val(data_size);
        divider = (update_time_new - rc_last_update)/1ns;
        divider = (divider != 0) ? divider : 4;
        rc_speed.next_val(real'(data_size)/divider);
        rc_last_update = update_time_new;
    endfunction

    virtual function void write_cq(uvm_pcie::request_header t);
        int unsigned data_size;
        const time update_time_new = $time();
        int unsigned divider;
        cq_packets += 1;

        data_size = t.data.size() + (t.fmt[0] == 1 ? 4 : 3);
        cq_data_size.next_val(data_size);
        divider = (update_time_new - cq_last_update)/1ns;
        divider = (divider != 0) ? divider : 1;
        cq_speed.next_val(real'(data_size)/divider);
        cq_last_update = update_time_new;
    endfunction

    virtual function void write_cc(uvm_pcie::completer_header t);
        int unsigned data_size;
        const time update_time_new = $time();
        int unsigned divider;
        cc_packets += 1;

        data_size = t.data.size() + 3;
        cc_data_size.next_val(data_size);
        divider = (update_time_new - cc_last_update)/1ns;
        divider = (divider != 0) ? divider : 1;
        cc_speed.next_val(real'(data_size)/divider);
        cc_last_update = update_time_new;
    endfunction

    task run_phase(uvm_phase phase);
        time information_stop;
        int unsigned section;
        rq_last_update = $time();
        rc_last_update   = $time();
        cq_last_update = $time();
        cc_last_update   = $time();

        //in inicialization this become start
        information_stop = $time();
        forever begin
            time information_start;
            real min;
            real max;
            real avg;
            real std_dev;
            string msg;

            //Init section
            information_start = information_stop;
            rq_packets = 0;
            rc_packets = 0;
            cq_packets = 0;
            cc_packets = 0;
            rq_speed.reset();
            rq_data_size.reset();
            rc_speed.reset();
            rc_data_size.reset();
            cq_speed.reset();
            cq_data_size.reset();
            cc_speed.reset();
            cc_data_size.reset();

            #(section_time);
            information_stop = $time();
            section++;

            msg = $sformatf("\nPCIE meter information time [%0dns, %0dns]\n", information_start/1ns, information_stop/1ns);
            msg = {msg, $sformatf("\n\trq packet %0d\n\trc packet %0d\n\tcq packet %0d\n\tcc packet %0d", rq_packets, rc_packets, cq_packets, cc_packets)};
            rq_data_size.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\n\tRQ DATA:\n\t\tMIN : %0.2f (%0.2f b) \n\t\tMAX : %0.2f (%0.2f b)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f b %0.2f b)\n", min, min*KOEF, max, max*KOEF, avg, std_dev, avg*KOEF, std_dev*KOEF)};
            rq_speed.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\tRQ SPEED :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n", min*KOEF, max*KOEF, avg*KOEF, std_dev*KOEF)};
            rc_data_size.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\n\tRC DATA:\n\t\tMIN : %0.2f (%0.2f b) \n\t\tMAX : %0.2f (%0.2f b)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f b %0.2f b)\n", min, min*KOEF, max, max*KOEF, avg, std_dev, avg*KOEF, std_dev*KOEF)};
            rc_speed.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\tRC SPEED :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n", min*KOEF, max*KOEF, avg*KOEF, std_dev*KOEF)};
            cq_data_size.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\n\tCQ DATA:\n\t\tMIN : %0.2f (%0.2f b) \n\t\tMAX : %0.2f (%0.2f b)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f b %0.2f b)\n", min, min*KOEF, max, max*KOEF, avg, std_dev, avg*KOEF, std_dev*KOEF)};
            cq_speed.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\tCQ SPEED :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n", min*KOEF, max*KOEF, avg*KOEF, std_dev*KOEF)};
            cc_data_size.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\n\tCC DATA:\n\t\tMIN : %0.2f (%0.2f b) \n\t\tMAX : %0.2f (%0.2f b)\n\t\tAVG STD_DEV : %0.2f %0.2f (%0.2f b %0.2f b)\n", min, min*KOEF, max, max*KOEF, avg, std_dev, avg*KOEF, std_dev*KOEF)};
            cc_speed.count(min, max, avg, std_dev);
            msg = {msg, $sformatf("\tCC SPEED :\n\t\tMIN : %0.2f Gb/s \n\t\tMAX : %0.2f Gb/s\n\t\tAVG STD_DEV : %0.2f Gb/s %0.2f Gb/s\n", min*KOEF, max*KOEF, avg*KOEF, std_dev*KOEF)};
            `uvm_info(this.get_full_name(), msg, UVM_LOW);            
        end
    endtask

endclass
