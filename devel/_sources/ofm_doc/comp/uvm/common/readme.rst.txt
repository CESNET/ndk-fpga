.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Common package
.. _uvm_common:

**************
Common package
**************

common package contain commonly used small components.


Random
------
Common randomization is required for generating space between frame and space between
packets. For this purpose two classes have been created (rand_rdy, rand_length). Fist class
generates rdy signal. Second class generate number reprezenting length.

There is class inheritance from rand_rdy and rand_length class. This class should be used
to generate better randomization. Class rand_rdy and rand_length is common interface.

Folowing example show commonly used for generating space between packet and interfame gaps

.. code-block:: SystemVerilog

    //simple sequence
    class sequence_simple extends uvm_sequence#(sequence_item);
        `uvm_object_utils(test::sequence_simple);
        uvm_common::rand_rdy    rdy;    //inter frame gabs
        uvm_common::rand_length space;  //space between frames
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            rdy   = uvm_common::rand_rdy_rand::new();
            space = uvm_common::rand_length_rand::new();
        endfunction
        task body();
            forever begin
                // generate space between frames
                space.randomize();
                for(int unsigned it = 0; it < space.m_value; it++) begin
                    send_empty_frame();
                end
                //send transaction
                hl_sequencer.get(hl_transaction);
                for (int unsigned it = 0; it < hl_transaction.data.size(); it++) begin
                    //send space inside frames
                    rdy.randomize();
                    while (rdy.m_value == 0) beign
                        send_empty_frame();
                    end
                    //send frames
                    send_frame(hl_transaction.data[it], it);
                end
            end
        endtask
        ...
    endclass


Comparer
--------

These components compare transactions from the DUT with transactions from the model.
There are three major classes. All classes have one required parameter and one optional parameter.
The first parameter is the type of model's transactions. The second parameter is the type of DUT transactions.

.. list-table:: comparer classes
   :widths: 400 400
   :header-rows: 1

   * - class
     - description
   * - uvm_common::comparer_base_ordered#(type MODEL_ITEM, DUT_ITEM = MODEL_ITEM)
     - The DUT output has to produce transactions in the same order as the model
   * - uvm_common::comparer_base_disordered#(type MODEL_ITEM, DUT_ITEM = MODEL_ITEM)
     - The DUT output doesn't have to produce transactions in the same order as the model
   * - uvm_common::comparer_base_tagged#(type MODEL_ITEM, DUT_ITEM = MODEL_ITEM)
     - The Dut output has to produce transactions in the same order as the model only for each tag. In other words, if the transactions were split per tag into separate streams (one stream for each tag), they must be in order within each stream.


If the type of the model and DUT transactions are the same, then a predefined comparer component can be used.
This component has only one parameter - the transaction type.

.. list-table:: comparer classes
   :widths: 200 
   :header-rows: 1

   * - class
   * - comparer_ordered #(type CLASS_TYPE)
   * - comparer_disordered #(type CLASS_TYPE)
   * - comparer_taged #(type CLASS_TYPE)

All comparers contain a watchdog. You can set up the maximum waiting time for the model and DUT transactions.
Maximum waiting time for the model transactions may be necessary if the DUT can create results from partial input.

.. list-table:: comparer classes
   :widths: 200 400
   :header-rows: 1

   * - function
     - description
   * - dut_tr_timeout_set(time timeout)
     - How much can the DUT transactions be delayed after the model's transactions (due to the DUT processing time)
   * - model_tr_timeout_set(time timeout)
     - How much can the model's transactions be delayed after the DUT transactions (due to a partial calculation)


The classes contain two analysis ports. The model's output is connected to the ``analysis_imp_model`` port.
The DUT's output is connected to the ``analysis_imp_dut`` port.
Anything else should be done by classes.

Also, there is the possibility of creating your own comparable algorithm and messages.
You can do this by reimplementing pure virtual functions:
``virtual function int unsigned compare(MODEL_TYPE tr_model, DUT_TYPE tr_dut);`` and
``virtual function void message(MODEL_TYPE tr_model, DUT_TYPE tr_dut);``.
``virtual function void message(MODEL_TYPE tr_model, DUT_TYPE tr_dut);`` The code below provides an example.

.. code-block:: SystemVerilog

    // The class extends a specified model and dut type of transactions.
    class scoreboard_channel_header #(HDR_WIDTH, META_WIDTH, CHANNELS, PKT_MTU) extends uvm_common::comparer_base_tagged #(packet_header #(META_WIDTH, CHANNELS, PKT_MTU), uvm_logic_vector::sequence_item#(HDR_WIDTH));
        `uvm_component_param_utils(uvm_app_core::scoreboard_channel_header #(HDR_WIDTH, META_WIDTH, CHANNELS, PKT_MTU))
    
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction
    
        // This method implements a comparison of these two types.
        virtual function int unsigned compare(packet_header #(META_WIDTH, CHANNELS, PKT_MTU) tr_model, uvm_logic_vector::sequence_item#(HDR_WIDTH) tr_dut);
            int unsigned eq = 1;
            logic [META_WIDTH-1:0]meta = 'x;
            logic [$clog2(CHANNELS)-1:0] channel;
            logic [$clog2(PKT_MTU+1)] packet_size;
            logic discard;
    
            if (META_WIDTH == 0) begin
                {discard, channel, packet_size} = tr_dut.data;
            end else begin
                {discard, channel, meta, packet_size} = tr_dut.data; 
            end
    
            eq &= (discard === tr_model.discard);
            eq &= (channel === tr_model.channel);
            if (META_WIDTH != 0) begin
                eq &= (meta    === tr_model.meta);
            end
            eq &= (packet_size === tr_model.packet_size);
    
            return eq;
        endfunction
    
        // This method implements error message printing when an error occurs.
        virtual function string message(packet_header #(META_WIDTH, CHANNELS, PKT_MTU) tr_model, uvm_logic_vector::sequence_item#(HDR_WIDTH) tr_dut);
            string error_msg; //ETH [%0d] header
            logic [META_WIDTH-1:0]meta = 'x;
            logic [$clog2(CHANNELS)-1:0] channel;
            logic [$clog2(PKT_MTU+1)] packet_size;
            logic discard;
    
            if (META_WIDTH == 0) begin
                {discard, channel, packet_size} = tr_dut.data;
            end else begin
                {discard, channel, meta, packet_size} = tr_dut.data; 
            end
            $swrite(error_msg, "\n\t\t          [DUT model]");
            $swrite(error_msg, "%s\n\t\tdiscard [%b %b]", error_msg, discard, tr_model.discard);
            $swrite(error_msg, "%s\n\t\tchannel [%0d %0d]", error_msg, channel, tr_model.channel);
            $swrite(error_msg, "%s\n\t\tmeta    [%h %h]", error_msg, meta, tr_model.meta);
            $swrite(error_msg, "%s\n\t\tpacket_size [%0d %0d]", error_msg, packet_size, tr_model.packet_size);
    
            return error_msg;
        endfunction
    endclass


