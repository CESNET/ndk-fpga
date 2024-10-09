.. readme.rst: Documentation of single component
.. Copyright (C) 2024 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. MVB agent and MVB interface
.. _uvm_probe:

************
probe agent
************

The purpose of this agent is to get information from the tested design. That information is commonly used in models to correct generated output. For example, to check the correct time when some pipelines in DUT are disabled or to change some rules for dropping packets.



Interface
^^^^^^^^^

The interface has one parameter and three signals. The parameter defines the width of the data signal. Signal **event_signal** is connected to a trigger. Signal **event_data** is connected to collected data. The last signal **CLK** is a clock. The trigger is evaluated when there is a rising edge of the clock.

.. code-block:: systemverilog

    interface probe_inf #(int unsigned DATA_WIDTH) (
        input wire logic event_signal,
        input wire logic [DATA_WIDTH-1:0] event_data,
        input wire logic CLK);

        ...
    endinterface


Bind
^^^^

The bind command creates an instance of an interface directly in a component. The bind command is divided into several parts. The first is a component name. The second is a path to the component. **probe_inf** is an interface name. **probe_status** is a bind name. The interface has three parameters. The first is a trigger. The second is sampled data. When the trigger is fired, data is sampled. The last parameter is a clock. All parameters are connected to the internal signals in a bound component.

.. code-block:: systemverilog

    // entity name : path to entity  probe_if #(DATA_WIDTH) ( trigger , data , CLOCK)
    bind FIFOX : VHDL_DUT_U probe_inf #(2) probe_status((RESET === 1'b0), { wr_en, rd_en }, CLK);



Callback
^^^^^^^^

The callback is called when there is a rising edge of the clock and the trigger is activated. The data is sampled at this point.

Callback class definition

.. code-block:: systemverilog

    class cbs_simple #(int unsigned DATA_WIDTH) extends uvm_event_callback;
        `uvm_object_param_utils(uvm_probe::cbs_simple #(DATA_WIDTH))
        logic [DATA_WIDTH-1:0] queue[$];

        function new(string name = "");
            super.new(name);
        endfunction

        // this callback is called just befor trigger. if this callback return 1
        // then function post_trigger is not goingt to be called.
        virtual function bit pre_trigger(uvm_event e, uvm_object data);
            return 0;
        endfunction

        // this function is called just after trigger.
        virtual function void post_trigger(uvm_event e, uvm_object data);
            uvm_probe::data#(DATA_WIDTH) c_data;
            logic wr_en;
            logic rd_en;

            $cast(c_data, data);
            //store data from probe
            queue.push_back(c_data.data);
            //{wr_en, rd_en} = c_data.data;
            //$write("GET WR EN(%b) and RD EN(%b)\n", wr_en, rd_en);
        endfunction

        // Model can get information stored in fifo
        task get(output logic wr_en, logic rd_en);
            logic [DATA_WIDTH-1:0] data;

            wait(queue.size() != 0);
            data = queue.pop_front();
            {wr_en, rd_en} = data;
        endtask
    endclass




Create and connect the callback to a model

.. code-block:: systemverilog

    // Model inputs
    // class #(DATA_WIDTH) variable_name
    uvm_probe::cbs_simple #(2) wr_and_rd_en_in;

    function void build_phase(uvm_phase phase);
        //create callback object
        wr_and_rd_en_in = uvm_probe::cbs_simple #(2)::type_id::create("wr_and_rd_en_in", this);
        //connect callback to the interface
        uvm_probe::pool::get_global_pool().get({ "probe_event_component_", "testbench.DUT_U.VHDL_DUT_U", ".probe_status" }).add_callback(wr_and_rd_en_in);
    endfunction

    task run_phase();
        logic wr_en;
        logic rd_en;

        forever begin
            ...
            //get data from the probe
            wr_and_rd_en_in.get(wr_en, rd_en);
            ...
        end
    endtask

