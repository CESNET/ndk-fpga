.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Radek Iša <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

..  logic_vector to mvb enviroment
.. _logic_vector_mvb:

****************************
logic_vector_mvb environment
****************************
This environment convert logic_vector transaction to mvb transactions.


The environment is configured by these four parameters: For more information see :ref:`mvb documentation<mvb_bus>`.

- ITEMS
- ITEMS_WIDTH

Top sequencers and sequences
------------------------------
In the RX direction, there is one sequencer that generates logic_vector transactions. The generated transactions will be randomly ordered and then converted to MVB transactions.

In the TX direction, there is one sequencer of type mvb::sequencer #() which generates the DST_RDY signal.

Both environments send logic_vector transactions through the analysis_export.


Configuration
------------------------------

The config class has three variables.

===============   ======================================================
Variable          Description
===============   ======================================================
active            Set to UVM_ACTIVE if the agent is active, otherwise set it to UVM_PASSIVE.
interface_name    The name of the interface under which you can find it in uvm config database.
seq_cfg           Configure a low-level sequence that converts logic_vector to MVB words.
===============   ======================================================

The top level environment contains the reset_sync class, which is required for reset synchronization. The example shows how to connect the reset to the logic_vector_array_mfb environment and its basic configuration.


.. code-block:: systemverilog

    class test extends uvm_test
        `uvm_componet_utils(test::base)
        reset::agent                m_resets;
        logic_vector_mvb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
             logic_vector_mvb::config_item m_cfg;

             m_resets = reset::agent::type_id::create("m_reset", this);

             m_cfg = new();
             m_cfg.active = UVM_ACTIVE;
             m_cfg.interface_name = "MFB_IF";
             m_cfg.meta_behav     = config_item::META_SOF;
             m_cfg.cfg = new();
             m_cfg.cfg.space_size_set(128, 1024);
             uvm_config_db#(logic_vector_mvb_env::config_item)::set(this, "m_eth", "m_config", m_cfg);
             m_env = logic_vector_mvb::env_rx#(...)::type_id::create("m_env", this);
        endfunction

         function void connect_phase(uvm_phase phase);
            m_reset.sync_connect(m_env.reset_sync);
         endfunction
    endclass


Low sequence configuration
--------------------------

The configuration object `config_sequence` contains one function.

=========================  ======================  ======================================================
Variable                   Type                    Description
=========================  ======================  ======================================================
space_size_set(min, max)   [bytes]                 Set min and max space between two logic_vector items in a MVB transaction.
=========================  ======================  ======================================================


RX Inner sequences
------------------------------

For the RX direction, there is one basic sequence class called "sequence_simple_rx_base", which simplifies creating other sequences. It processes the reset signal and exports the create_sequence_item virtual
function. In this function, a child can create a mvb::sequence_item as they like.

The environment has three sequences. The table below describes them. In the default state, the RX env runs sequence_lib_rx.

==========================       ======================================================
Sequence                         Description
==========================       ======================================================
sequence_rand_rx                 A basic random sequence. This sequence behaves very variably.
sequence_burst_rx                The sequence sends data in bursts.
sequence_full_speed_rx           The sequence gets data and then sends them as quickly as possible.
sequence_stop_rx                 This sequence doesn't send any data. There are no data on the interface.
sequence_lib_rx                  Repetitively Randomly choose one of the sequences above and run it.
==========================       ======================================================


    The example below shows how to change the inner sequence to test the maximum throughput. The environment runs the sequence_full_speed_rx sequence instead of the sequence_lib_rx.


.. code-block:: systemverilog

    class mvb_rx_speed#(...) extends logic_vector_mvb_env::sequence_lib_rx#(...);

        function new(string name = "mvb_rx_speed");
            super.new(name);
            init_sequence_library();
        endfunction

        virtual function void init_sequence(config_sequence param_cfg = null);
            if (param_cfg == null) begin
                this.cfg = new();
            end else begin
                this.cfg = param_cfg;
            end
            this.add_sequence(logic_vector_mvb_env::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        endfunction
    endclass


    class test extends uvm_test
        `uvm_componet_utils(test::base)
        logic_vector_mvb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            ...
             logic_vector_mvb_env::sequence_lib_rx#(...)::type_id::set_inst_override(mvb_rx_speed#(...)::get_type(),
             {this.get_full_name(), ".m_env.*"});
             m_env = logic_vector_mvb::env_rx#(...)::type_id::create("m_env", this);
        endfunction
    endclass
