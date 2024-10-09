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
   * - uvm_common::comparer_base_unordered#(type MODEL_ITEM, DUT_ITEM = MODEL_ITEM)
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
   * - comparer_unordered #(type CLASS_TYPE)
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

fifo
----

This component has been created for connecting models. The problem is when there is an output value of one model changes before entering another model.
A common example is when the same model is used in the verification multiple times, and each time, its input(s) are modified differently. Such a scenario is displayed in the example below.


.. code-block:: VHDL

        ENTITY_i : entity work.ENTITY_A
        port map(
            CLK    => RX_CLK,
            RESET  => RX_RESET,

            DO     => ea_do
        );

        eb1_di <= ea_do +10;
        ENTITY_B1_i : entity work.ENTITY_B
        port map(
            CLK    => RX_CLK,
            RESET  => RX_RESET,

            DI     => eb1_di
            DO     => eb1_do
        );

        eb2_di <= ea_do +20;
        ENTITY_B2_i : entity work.ENTITY_B
        port map(
            CLK    => RX_CLK,
            RESET  => RX_RESET,

            DI     => eb2_di
            DO     => eb2_do
        );

The code below shows the scoreboard for the model connection.

.. code-block:: SystemVerilog

    class fifo_en1_input extends uvm_common::fifo#(model_item#(uvm_logic_vector#(32)));
        `uvm_component_utils(fifo_en1_input);

        uvm_analysis_imp_export#(model_item#(uvm_logic_vector#(32)), fifo_en1_input) analysis_export;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            analysis_export = new("analysis_expoert", this);
        endfunction

        function void write(model_item#(uvm_logic_vector#(32)) t);
            model_item#(uvm_logic_vector#(32)) item;

            item      = model_item#(uvm_logic_vector#(32))::type_id::create("item", this);
            item.item = uvm_logic_vector#(32)::type_id::create("item", this);

            item.tag   = t.tag;
            item.start = t.start;
            item.item.data = t.item.data + 10;
            this.push_back(item);
        endfunction
    endclass

    class fifo_en2_input extends uvm_common::fifo#(model_item#(uvm_logic_vector#(32)));
        `uvm_component_utils(fifo_en1_input);

        uvm_analysis_imp_export#(model_item#(uvm_logic_vector#(32)), fifo_en2_input) analysis_export;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            analysis_export = new("analysis_expoert", this);
        endfunction

        function void write(model_item#(uvm_logic_vector#(32)) t);
            model_item#(uvm_logic_vector#(32)) item;

            item      = model_item#(uvm_logic_vector#(32))::type_id::create("item", this);
            item.item = uvm_logic_vector#(32)::type_id::create("item", this);

            item.tag   = t.tag;
            item.start = t.start;
            item.item.data = t.item.data + 20;
            this.push_back(item);
        endfunction
    endclass

    class model_entityb extends uvm_component;
        `uvm_component_utils(model_entityb);

        uvm_common::fifo#(model_item#(uvm_logic_vector#(32))) in;

        function new(string name, uvm_component parent);
            super.new(name, parent);
            in = null;
        endfunction

        ....
    endclass

    class scoreboard extends uvm_scoreboard;
        `uvm_component_utils(scoreboard);

        model_A m_model_a;
        model_B m_model_b1;
        model_B m_model_b2;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            m_model_a  = model_A::type_id::create("m_model_a", this);
            m_model_b1 = model_B::type_id::create("m_model_b1", this);
            m_model_b1.in = fifo_en1_input::type_id::create("in", m_model_b1);
            m_model_b2 = model_B::type_id::create("m_model_b2", this);
            m_model_b2.in = fifo_en2_input::type_id::create("in", m_model_b2);
        endfunction

        function void connect_phase(uvm_phase phase);
            fifo_en1_input mb1_in;
            fifo_en2_input mb2_in;

            $cast(mb1_in, m_model_b1.in);
            m_model_a.do.connect(mb1_in.analysis_export);
            $cast(mb2_in, m_model_b2.in);
            m_model_a.do.connect(mb2_in.analysis_export);
        endfunction
    endclass


Also, there is the possibility of merging two inputs into one. When something. The code below shows an example of an input FIFO which merges two inputs into one.

.. code-block:: SystemVerilog

    class m_fifo_input extends uvm_common::fifo#(model_item#(uvm_logic_vector#(32)));
        `uvm_component_utils(m_fifo_input);

        uvm_tlm_analysis_fifo#(model_item#(uvm_logic_vector#(16)), m_fifo_input) in_a;
        uvm_tlm_analysis_fifo#(model_item#(uvm_logic_vector#(16)), m_fifo_input) in_b;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            in_a = new("in_a", this);
            in_b = new("in_b", this);
        endfunction

        task run_phase(uvm_phase);
            model_item#(uvm_logic_vector#(16)) tr_in_a;
            model_item#(uvm_logic_vector#(16)) tr_in_b;

            model_item#(uvm_logic_vector#(32)) tr_out;

            forever begin
                in_a.get(tr_in_a);
                in_b.get(tr_in_b);

                tr_out      = model_item#(uvm_logic_vector#(32)::type_id::create("tr_out", this);
                tr_out.item = uvm_logic_vector#(32)::type_id::create("tr_out.item", this);

                tr_out.time_array_add(tr_in_a.start);
                tr_out.time_array_add(tr_in_b.start);
                tr_out.tag  = {"M1_", tr_in_b.tag};
                tr_out.item.data = {tr_in_b.item.data, tr_in_a.item.data};
                this.push_back(tr_out);
            end
        endtask
    endclass
