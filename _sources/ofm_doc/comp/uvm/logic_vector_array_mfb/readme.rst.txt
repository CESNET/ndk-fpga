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
This enviroment have two high level agents. First agents is logic vector array and it is care about data. Second high level acent is logic vector wchich care about metadata.
This package containt two enviroment. Enviroment RX sending data to DUT. It generatest data and metadata which is send to DUT. Enviroment TX generatest DST_RDY and
observed interface.

.. image:: ../docs/byte_array_mfb_env.svg
    :align: center
    :alt: logic_vector_array_mfb schema


The environment is configured by four parameters: For more information see :ref:`mfb documentation<mfb_bus>`.

============== =
Parameter
============== =
REGIONS
REGIONS_SIZE
BLOCK_SIZE
ITEM_SIZE
META_WIDTH
============== =

Top sequencers and sequences
------------------------------
In the RX direction there are two sequencers: the first is Logic vector array sequencer and handles MFB_DATA, the second is logic vector sequencer and handles MFB_METADATA. Both sequencers pulls the data from sequences together.

In the TX direction there is one sequencer of type mfb::sequencer #() which generate DST_RDY signal.

Both directions have two analysis_exports. One export is for logic vector array transactions. Second is for logic vector (metadata) transactions.


Configuration
------------------------------

config class have 3 variables.

===============   ======================================================
Variable          Description
===============   ======================================================
active            Set to UVM_ACTIVE if agent is active otherwise UVM_PASSIVE
interface_name    name of interface under which you can find it in uvm config database
meta_behave       Moment of Metadata signal is being generated and valid: 1 => valid with the SOF. 2 => valid with the EOF.
seq_cfg           Configure low leve sequence which convert logic_vector_array to mfb words
===============   ======================================================

Top level of environment contains reset_sync class which is required for reset synchronization. The example shows how to connect the reset to logic_vector_array_mfb environment and basic configuration.

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
             m_cfg.meta_behav     = 1;
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

configuration object `config_sequence` contain two function.

=========================  ======================  ======================================================
Variable                   Type                    Description
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


The environment have three sequences. Table below describes them. In default RX env runs sequence_lib_rx.

==========================       ======================================================
Sequence                         Description
==========================       ======================================================
sequence_simple_rx               base random sequence. This sequence is behavioral very variably.
sequence_full_speed_rx           if sequence get data then send them as quicky as possible.
sequence_stop_rx                 Sequence dosnt send any data. Sumulate no data on interface.
sequence_lib_rx                  randomly run pick and run previous sequences
==========================       ======================================================


    An example below shows how to change the inner sequence to test maximal throughput. Environment run the sequence_full_speed_rx instead of the sequence_lib_rx.

.. code-block:: systemverilog

    class mfb_rx_speed#(...) extends logic_vector_array_mfb_env::sequence_lib_rx#(...);

        function new(string name = "mfb_rx_speed");
            super.new(name);
            init_sequence_library();
        endfunction

        virtual function void init_sequence();
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
