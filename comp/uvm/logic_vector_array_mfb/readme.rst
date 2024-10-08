.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Radek Iša <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

..  logic_vector_array to mfb enviroment
.. _logic_vector_array_mfb_mfb:

**********************************
logic_vector_array_mfb environment
**********************************
This environment has two high-level agents. The first one is a logic vector array agent and it works with data. The second one is a logic vector agent which works with metadata.
This package contains two environments. Environment RX generates data and metadata and sends them to the DUT. Environment TX generates the DST_RDY signal and
observes the TX interface.


.. image:: ../docs/byte_array_mfb_env.svg
    :align: center
    :alt: logic_vector_array_mfb schema


The environment is configured by these four parameters: For more information see :ref:`mfb documentation<mfb_bus>`.

- REGIONS
- REGIONS_SIZE
- BLOCK_SIZE
- ITEM_SIZE
- META_WIDTH

op sequencers and sequences
------------------------------
In the RX direction, there are two sequencers: the first is a Logic vector array sequencer that handles MFB_DATA.
The second is a logic vector sequencer that handles MFB_METADATA. Both sequencers pull the data from sequences together.

In the TX direction, there is one sequencer of type mfb::sequencer #(), which generates the DST_RDY signal.

Both directions have two analysis_exports. One export is for the logic vector array transactions, and the second is for the logic vector (metadata) transactions.


Configuration
------------------------------

The config class has three variables.

===============   ======================================================
Variable          Description
===============   ======================================================
active            Set to UVM_ACTIVE if the agent is active, otherwise set to UVM_PASSIVE.
interface_name    The name of the interface under which you can find it in the UVM config database.
meta_behave       The moment when the metadata are being generated and are valid: config_item::META_SOF => valid with the SOF, config_item::META_EOF => valid with the EOF.
seq_cfg           Configure a low-level sequence that converts logic_vector_array to MFB words.
===============   ======================================================

The top level of the environment contains the reset_sync class, which is required for reset synchronization. The example shows how to connect the reset to the logic_vector_array_mfb environment and basic configuration.


.. code-block:: systemverilog

    class test extends uvm_test
        `uvm_componet_utils(test::base)
        reset::agent                m_resets;
        logic_vector_array_mfb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
             logic_vector_array_mfb::config_item m_cfg;

             m_resets = reset::agent::type_id::create("m_reset", this);

             m_cfg = new();
             m_cfg.active = UVM_ACTIVE;
             m_cfg.interface_name = "MFB_IF";
             m_cfg.meta_behav     = config_item::META_SOF;
             m_cfg.cfg = new();
             m_cfg.cfg.space_size_set(128, 1024);
             uvm_config_db#(logic_vector_array_mfb_env::config_item)::set(this, "m_eth", "m_config", m_cfg);
             m_env = logic_vector_array_mfb::env_rx#(...)::type_id::create("m_env", this);
        endfunction

         function void connect_phase(uvm_phase phase);
            m_reset.sync_connect(m_env.reset_sync);
         endfunction
    endclass


Low sequence configuration
--------------------------

The configuration object `config_sequence` contains two functions.

=========================  ======================  ======================================================
Variable                   Type                    Description
=========================  ======================  ======================================================
probability_set(min, max)  [percentage]            Set the probability of no inframe gap: probability_set(100,100) => no inframe gap at all.
space_size_set(min, max)   [bytes]                 Set min and max space between two packets.
=========================  ======================  ======================================================


RX Inner sequences
------------------------------

For the RX direction, there is one basic sequence class called the "sequence_simple_rx_base" which simplifies creating other sequences. It processes the reset signal and exports the virtual
function create_sequence_item. In this function, a child can create mfb::sequence_items as they like. Another important function in the "sequence_simple_rx_base" class is try_get() which
gets the required data from the base array agent. It is also important to note that the base class is state-oriented. The following table describes internal states.

==========================    ======================================================
State                         Description
==========================    ======================================================
state_packet_none             No data for the packet.
state_packet_new              The try_get function has read a new packet.
state_packet_data             The process is somewhere in the middle of a packet.
state_pakcet_space            The process sends all data and generates a space before the new packet.
state_packet_space_new        Randomize a new space size before the new packet.
==========================    ======================================================


The environment has three sequences. The table below describes them. In the default state, the RX env runs sequence_lib_rx.

==========================       ======================================================
Sequence                         Description
==========================       ======================================================
sequence_simple_rx               A basic random sequence. This sequence behaves very variably.
sequence_full_speed_rx           The sequence gets data and then sends them as quickly as possible.
sequence_stop_rx                 This sequence doesn't send any data. There are no data on the interface.
sequence_lib_rx                  Repetitively Randomly choose one of the sequences above and run it.
==========================       ======================================================


    The example below shows how to change the inner sequence to test the maximum throughput. The environment runs the sequence_full_speed_rx sequence instead of the sequence_lib_rx.

.. code-block:: systemverilog

    class mfb_rx_speed#(...) extends logic_vector_array_mfb_env::sequence_lib_rx#(...);

        function new(string name = "mfb_rx_speed");
            super.new(name);
            init_sequence_library();
        endfunction

        virtual function void init_sequence(config_sequence param_cfg = null);
            if (param_cfg == null) begin
                this.cfg = new();
            end else begin
                this.cfg = param_cfg;
            end
            this.add_sequence(logic_vector_array_mfb_env::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        endfunction
    endclass


    class test extends uvm_test
        `uvm_componet_utils(test::base)
        logic_vector_array_mfb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            ...
             logic_vector_array_mfb_env::sequence_lib_rx#(...)::type_id::set_inst_override(mfb_rx_speed#(...)::get_type(),
             {this.get_full_name(), ".m_env.*"});
             m_env = logic_vector_array_mfb::env_rx#(...)::type_id::create("m_env", this);
        endfunction
    endclass
