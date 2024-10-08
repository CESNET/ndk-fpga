/*
 * file       : pool.sv
 * Copyright (C) 2023 CESNET z. s. p. o.
 * description: event pool
 * date       : 2023
 * author     : Radek Iša <isa@cesnet.ch>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class pool extends uvm_object_string_pool #(uvm_event);

    typedef pool this_type;
    static protected this_type m_global_pool;

    function new (string name="");
        super.new(name);
    endfunction


    const static string type_name = {"uvm_probe::pool"};

    virtual function string get_type_name();
        return type_name;
    endfunction

    virtual function uvm_event get(string key);
        if (!m_global_pool.exists(key)) begin
            string items;
            items = "";
            foreach (m_global_pool.pool[it]) begin
                items = {items, "\t", it, "\n"};
            end
           `uvm_fatal(this.get_full_name(), {"Probe : ", key , " was not located in the Global Pool of Probes! Check the name of your Probe.\nAccessible events:\n", items});
        end

        return super.get(key);
    endfunction

    static function this_type get_global_pool ();
        if (m_global_pool==null)
            m_global_pool = new("global_pool");
        return m_global_pool;
    endfunction
endclass

