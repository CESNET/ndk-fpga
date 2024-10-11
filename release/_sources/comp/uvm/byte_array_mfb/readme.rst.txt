.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Byte array to mfb enviroment
.. _uvm_byte_array_mfb:

**************************
Byte_array_mfb environment
**************************
This environment has two high-level agents. The first one is a byte array agent and it works with data. The second one is a logic vector agent which works with metadata.
This package contains two environments. Environment RX generates data and metadata and sends them to the DUT. Environment TX generates the DST_RDY signal and
observes the TX interface.

.. image:: ../docs/byte_array_mfb_env.svg
    :align: center
    :alt: byte array mfb schema


The environment is configured by these four parameters: :ref:`mfb documentation<mfb_bus>`.

- REGIONS
- REGIONS_SIZE
- BLOCK_SIZE
- META_WIDTH

Top sequencers and sequences
------------------------------
In the RX direction, there are two sequencers: the first is a Byte Array sequencer that handles MFB_DATA.
The second is a Logic Vector sequencer that handles MFB_METADATA. Both sequencers pull the data from sequences together.

In the TX direction, there is one sequencer of type mfb::sequencer #(), which generates the DST_RDY signal.

Both directions have two analysis_exports. One export is for the Byte Array transactions, and the second is for the Logic Vector (metadata) transactions.


Configuration
------------------------------

The config class has three variables.

===============   ======================================================
Variable          Description
===============   ======================================================
active            Set to UVM_ACTIVE if the agent is active, otherwise set to UVM_PASSIVE.
interface_name    The name of the interface under which you can find it in the UVM config database.
meta_behave       The moment when the metadata are being generated and valid: config_item::META_SOF => valid with the SOF, config_item::META_EOF => valid with the EOF.
seq_cfg           Configure a low-level sequence that converts byte_array to MFB words.
===============   ======================================================

The top level the environment contains the reset_sync class, which is required for reset synchronization. The example shows how to connect the reset to the byte_array_mfb environment and basic configuration.


.. code-block:: systemverilog

    class test extends uvm_test
        `uvm_componet_utils(test::base)
        reset::agent                m_resets;
        byte_array_mfb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
             byte_array_mfb::config_item m_cfg;

             m_resets = reset::agent::type_id::create("m_reset", this);

             m_cfg = new();
             m_cfg.active = UVM_ACTIVE;
             m_cfg.interface_name = "MFB_IF";
             m_cfg.meta_behav     = config_item::META_SOF;
             m_cfg.cfg = new();
             m_cfg.cfg.space_size_set(128, 1024);
             uvm_config_db#(byte_array_mfb_env::config_item)::set(this, "m_eth", "m_config", m_cfg);
             m_env = byte_arra_mfb::env_rx#(...)::type_id::create("m_env", this);
        endfunction

         function void connect_phase(uvm_phase phase);
            m_reset.sync_connect(m_env.reset_sync);
         endfunction
    endclass


Low sequence configuration
--------------------------

configuration object `config_sequence` contain two function.

=========================  ======================  ======================================================
Function                   Type                    Description
=========================  ======================  ======================================================
probability_set(min, max)  [percentige]            set probability of no inframe gap. probability_set(100,100) => no inframe gap
space_size_set(min, max)   [bytes]                 set min and max space between two packets.
=========================  ======================  ======================================================


RX Inner sequences
------------------------------

For the RX direction exists one base sequence class "sequence_simple_rx_base" which simplifies creating others sequences. It processes the reset signal and exports virtual
function create_sequence_item. In this function can child create mfb::sequence_item what they like. Other important function in "sequence_simple_rx_base" class is try_get() which
downloads required data from base array agent. It is also important to note that the base class is state oriented. Following table describes internal states.

==========================    ======================================================
State                         Description
==========================    ======================================================
state_packet_none             No data for packet
state_packet_new              new packet has been read by function try_get
state_packet_data             process is somewhere in middle of packet
state_pakcet_space            Process send all data and generate space before new packet
state_packet_space_new        Randomize new space size before new packet
==========================    ======================================================


The environment has three sequences. The table below describes them. In the default, the RX env runs sequence_lib_rx.

==========================       ======================================================
Sequence                         Description
==========================       ======================================================
sequence_simple_rx               A basic random sequence. This sequence behaves very variably.
sequence_full_speed_rx           The sequence gets data and then sends them as quickly as possible.
sequence_stop_rx                 This sequence doesn't send any data. There are no data on the interface.
sequence_lib_rx                  Repetitively randomly choose one of the sequences above and run it.
==========================       ======================================================


    The example below shows how to change the inner sequence to test the maximum throughput. The environment runs the sequence_full_speed_rx instead of the sequence_lib_rx.


.. code-block:: systemverilog

    class mfb_rx_speed#(...) extends byte_array_mfb_env::sequence_lib_rx#(...);

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
            this.add_sequence(byte_array_mfb_env::sequence_full_speed_rx #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)::get_type());
        endfunction
    endclass


    class test extends uvm_test
        `uvm_componet_utils(test::base)
        byte_arra_mfb::env_rx#(...) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            ...
             byte_array_mfb_env::sequence_lib_rx#(...)::type_id::set_inst_override(mfb_rx_speed#(...)::get_type(),
             {this.get_full_name(), ".m_env.*"});
             m_env = byte_arra_mfb::env_rx#(...)::type_id::create("m_env", this);
        endfunction
    endclass
