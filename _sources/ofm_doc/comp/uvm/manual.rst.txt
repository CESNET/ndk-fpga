.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. UVM Manual
.. _uvm_manual:

****************
Manual
****************
This is manual how to write UVM verification in our enviroment.

SystemVerilog and UVM tutorial
##############################

This documents describes how should be written the UVM verification of our components. This is not UVM or SystemVerilog manual. UVM tutorials you can find on folowing links

- `systemverilog tutorial <http://www.asic-world.com/systemverilog/tutorial.html>`_
- `UVM tutorial <https://verificationguide.com/uvm/uvm-tutorial/>`_
- `UVM user guide <https://www.accellera.org/images/downloads/standards/uvm/uvm_users_guide_1.2.pdf>`_
- `Doulos coding guidelines <https://www.doulos.com/media/1277/easier-uvm-coding-guidelines-2016-06-24.pdf>`_
- `Packing <https://www.amiq.com/consulting/2017/05/29/how-to-pack-data-using-systemverilog-streaming-operators/>`_
- `Unpacking <https://www.amiq.com/consulting/2017/06/23/how-to-unpack-data-using-the-systemverilog-streaming-operators/>`_
- `systemverilog Assertion (asic-world) <http://www.asic-world.com/systemverilog/assertions.html>`_
- `systemverilog Assertion (einfochips) <https://www.einfochips.com/blog/system-verilog-assertions-simplified/>`_


Basic usage of UVM methodology in OFM
#####################################


This document describes one of the possible solutions of some common verification issues.



Interface
===========

Interface connects DUT with test. In interface is required to use **wire logic** instead of **logic** if there is no strong reason to do otherwise. **Wire logic** is net but **logic** is variable.
Reason of this solution is fact that we want to use one interface for RX and TX comunication. If you want to know more visit `wire logic vs logic <https://blogs.sw.siemens.com/verificationhorizons/2013/05/03/wire-vs-reg/>`_
It is required to use clocking block in interface if there is no strong reason to do otherwise.
Also interfaces dosn't have namespaces. This means that interfaces must have unique names.


Properties
==========

DUT comunicate with surroundings by some protocols which can have some restristions. These restriction can be controlled by module properties
which can be instantiate and connect to interface. Module then control if DUT keeps rules of these comunication protocol.

.. code-block:: systemverilog

    modules mfb_properties (input logic RESET, mfb_if RX_MFB);
        property prop_rdy;
            (posedge RX_FB.CLK) disable iff(RESET == 1'b1)
            !$isunknown(MFB_IF.DST_RDY) && !$isunknown(MFB_IF.SRC_RDY);
        endproperty

        assert property (prop_rdy) else begin `uvm_fatal("MFB INTERFACE: src and dst rdy have to be always valid\n") end
    endmodule


Driver
===========

Driver writes data to interface. It is required to use function **try_get** or **try_next_item** to get next item. Do not use function **get** or **get_next_item**.
If some sequencer uses for example wait *#(4ns)*, it can desynchronize driver with clocking block and race condition can happen.

Example of sequence with space 40ns space between sended items

.. code-block:: systemverilog

    class sequence_simple extends uvm_sequence#(sequence_item);
        `uvm_object_utils(pkg::sequence_simple)

        function new(string name);
            super.new(name);
        endfunction

        taks body ();
            req = sequence_item::tpye_id::create("req");
            for (int unsigned it = 0; it < 10 it++) begin
                start_item(req);
                req.randomize();
                finish_item(req);
                #(10)ns // this can desincronize driver and broke protocol. if task get is used instead of function try get.
            end
        endtask
    endclass


.. code-block:: systemverilog

    class driver extends uvm_driver#(sequence_item);
        `uvm_componet_utils(pkg::driver)
        virtual interface vif;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        taks run_phase (uvm_phase phase);
            forever begin
                seq_item_port.try_next_item(req);
                if (req != null) begin
                    vif.cb.data <= req.data;
                    seq_item_port.item_done();
                end else begin
                    vif.cb.data <= 'x;
                end
                @(vif.cb);
            end
        endtask
    endclass


Agent
===========

Pleas keep following rules for creating agents, enviroments and pakcage.

1. Use name of class together with package name in the UVM registation macro.
2. The name of class would be *monitor, driver, sequencer, config, sequence_item*. A suffix such as *_rx, _tx* can be used if required.
3. For the sequences, use *sequence_* prefix.
4. Variable names should have the prefix *m_*.
5. Files have the same name as class inside file. Every agent is placed into his own directory togeter with package *pkg.sv* and interface *interface.sv* if the interface is required

.. code-block:: systemverilog

    class agent extends uvm_agent;
        `uvm_component_utils( example::agent )
        uvm_analysis_port#(sequence_item) analysis_port;
        config m_config;
        sequencer m_sequencer;
        driver    m_driver;
        monitor   m_monitor;
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(config)::get(this, "", "m_config", m_config))
                `uvm_fatal(...);
            // First parametr name has to be same string as variable name
            m_monitor = monitor::type_id::create("m_monitor", this);
            if (m_config.active == ACTIVE) begin
                m_driver  = driver::type_id::create("m_driver", this);
                m_sequencer = sequencer::type_id::create("m_sequencer", this);
            end
        endfunction

        function void connect_phase(uvm_phase phase);
            virtual axi_lite_interface #(ADDR_WIDTH, DATA_WIDTH) vif;
            super.connect_phase(phase);
            if (uvm_config_db#(virtual axi_lite_interface#(ADDR_WIDTH, DATA_WIDTH))::get(this, "", "interface", vif) == 0) begin
                `uvm_fatal(this.get_full_name(), "Virtual interface axi_lite_interface havent been found.");
            end
            m_monitor.vif = vif;
            analysis_port = m_monitor.analysis_port;
            if (m_config.active == ACTIVE) begin
                m_driver.vif = vif;
                m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
            end
        endfunction
    endclass

Configuration object
====================

Every agent has his own configuration object, which can change agent behavioral.
There are two most common variables in the configuration object.
The first one is *active* which represents if the agent is active or passive. Active agent contain driver and it activly drive comunication on interface.
Passive agetnt is used just for observation of comunication on interface.
The second one is *interface_name* in case of direct communication between agent and DUT. Agent finds the correct interface in UVM configuration database save under *interface_name*.

Sequence
===========

The sequence contains three functions, which can change the randomization output (pre_do, mid_do, post_do).
Function pre_do is called before randomization. It is suitable for changing randomization rules.
Function mid_do is called after randomization and before the result is send to the driver.
This is suitable for setup of a specific value which could be difficult to randomize.
Function post_do is called after the driver processes transaction. It is suitable for generating statistic
or something else.

.. code-block:: systemverilog

    class config_sequence extends config::simple_simple;
        `uvm_object_utils(seq::config_sequence)
        function new (string name = "");
          super.new(name);
        endfunction

        virtual function pre_do(uvm_sequence_item this_item);
            //this happen before randomization
            this_item.size_max = max + 10;
        endfunction

        virtual function mid_do(uvm_sequence_item this_item);
            //this happen after randomization
            this_item.addr = addr++;
        endfunction

        virtual function post_do(uvm_sequence_item this_item);
            //this happen after sequence item has been processed
            cfg.add(this_item.data);
        endfunction
    endclass

Sequence library
================

For all agents is recommended to create a sequence library with some different sequences.
More sequences helps to uncover more bugs and rise coverage with small effort.
Sequence library randomly select sequence and run it on current seqeuncer.
This is repeated until sequence_library run required number of sequences.
Different sequence can randomly create different test scenarions like
burst mode, send small packet, send big packets, read or write sequently or on same address and others.

.. code-block:: systemverilog

    class sequence_packet_small extends uvm_sequence #(sequence_item);
        `uvm_object_utils(example::sequence_packet_small)

         rand int unsigned transactions;
            constraints c_transactions{
                transactions inside {[100:2000]};
            }

        function new (string name = "");
            super.new(name);
        endfunction

        task body();
            req = sequence_item#(C_CHAR_WIDTH)::type_id::create("req");
            for (int unsigned it = 0; it < transactions; it++) begin
                start_item(req);
                req.randomize() with {data.size() inside [1:10]};
                finish_item(req);
            end
        endtask
    endclass

.. code-block:: systemverilog

    class sequence_packet_large extends uvm_sequence #(sequence_item);
        `uvm_object_utils(example::sequence_packet_large)

        rand int unsigned transactions;
            constraints c_transactions{
                transactions inside {[100:2000]};
            }

        function new (string name = "");
            super.new(name);
        endfunction

        task body();
            req = sequence_item#(C_CHAR_WIDTH)::type_id::create("req");
            for (int unsigned it = 0; it < transactions; it++) begin
                start_item(req);
                req.randomize() with {data.size() inside [10000:200000]};
                finish_item(req);
            end
        endtask
    endclass

Creation of sequence library

.. code-block:: systemverilog

    class sequence_lib extends uvm_sequence_library#(sequence_item);
        `uvm_object_utils(example::sequence_lib)
        `uvm_sequence_library_utils(example::sequence_lib)

        function new(string name = "");
            super.new(name)
            init_sequence_library();
        endfunction

        // subclass can redefine and change run sequences
        // can be useful in specific tests
        virtual function init_sequence();
            this.add_sequence(sequence_packet_large::get_type());
            this.add_sequence(sequence_packet_small::get_type());
        endfunction
    endclass

run in environment or test

.. code-block:: systemverilog

    class env extends uvm_env
        ...
        taks run_phase(uvm_phase phase);
            sequence_lib seq = sequence_lib::type_id::create("sequence_lib");
            sequence_lib.init_sequence();
            if(!sequence_lib.randomize())
                `uvm_fatal (...);
            sequence_lib.start(m_agent.m_sequencer);
        endtask
        ...
    endclass

Package
===========

In all registration macros \`uvm_components_``*`` \`uvm_object_``*`` is required to use class name together with package name.
**\`uvm_components_utils(pkg::class)**

.. warning::

    If you don't register a component with package name, the verification can instantiate wrong class and verification behavioral can act strangely.

The verification code should use namespaces. Do not use **import pkg::``*``** command until it is necessary.
The only situation where you can use it is the import of uvm_package.


Layered agents
###################################

The most of the verification tests doesn't need to generate low level data.
For this purpose exist the high level generators which can generate packets.
This approach unifies the high level packet and separete it from from a low level protocol.
For a layered agent it is good way to use a pointer to high sequencer from low level sequence.
For this approach is required to know design pattern called *abstract factory* and how it is used in UVM methodology.


Environment
===========

The environment logically groups together other environments and agents.
In this case the environment groups high and low level agents. Required steps are:
1. Registration of a new high level monitor which completes a high level transaction from the low level transactions.
2. Creating a low level sequence which pulls high level sequence items from high level sequencer and generate low level transactions from high level sequence items
3. Use the second argument when creating sequence or sequence_library because it simplify run specific sequence for specific tests.

.. image:: ./docs/layered_agents.svg
    :align: center
    :alt: layered agents


.. code-block:: systemverilog

    class env extends uvm_env;
        ...

        function void build_phase(uvm_phase phase);
            //change common monitor to specific monitor
            byte_array_moinitor::type_id::set_inst_override(byte_array_mfb_monitor::get_type(), {this.get_full_name(), ".m_byte_array_agent.*"});
            super.build_phase(phase);
            m_byte_array_agent = byte_array_agent::type_id::create("m_byte_array_agent", this);
            m_mfb_agent        = mfb_agent::type_id::create("m_mfb_agent", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            byte_array_mfb_monitor mon;
            $cast(mon, m_byte_array_agent.m_monitor);
            m_mfb_agent.analysis_port.connect(mon.analysis_imp);
            analysis_port = m_byte_array_agent.m_monitor.analysis_port;
            m_sequencer   = m_byte_array_agent.m_sequencer;
        endfunction

        task run_phase(uvm_phase phase);
            // It is recomended use sequence library
            byte_array_mfb_sequence seq;
            seq = byte_array_mfb_sequence::type_ide::create("seq", this);
            seq.hl_sequencer = m_byte_array_agent.m_sequencer;
            forever begin
                seq.randomize();
                seq.start(m_mfb_agent.m_sequencer);
            end
        endtask
    endclass


Low level sequence
==================

The purpose of low-level sequence is to create low level sequence_items from high-level sequence_item. For example we use byte array as high level sequence_item and 32bit word as low level transaction.
Folowing example shows how to parse the high level items into the low level items using the for cycle. Low level sequence is going to be run in environment in the *run_phase* task as show previous example.

.. code-block:: systemverilog

    task body()
        forever begin
            //get higher level transactin from higher level sequencer
            hl_sequencer.get_next_item(hl_item);
            //break hl_item into lower level transaction
            for (int unsigned it = 0; it < hl_item.data.size(); it += WORD_SIZE) begin
                start_item(req);
                req.data = { << 8{hl_item.data[it +: WORD_SIZE]}};
                req.sof = 1'b0;
                req.eof = 1'b0;
                if (it == 0)
                    req.sof = 1'b1;
                if (it + WORD_SIZE >= hl_item.data.size())
                    req.eof = 1'b1
                finish_item(req);
            end
            //send item done to higher level sequencer
            hl_sequencer.item_done();
        end
    endtaks


High level monitor
==================

The purpose of high level monitor is to create a high level sequence_item from a low level sequence_items.
Unfortunately the general high level monitor cannot cooperate with low level transaction.
Therefore the common approach is to reimplement a high level monitor and use UVM configuration database as shows the previous example. Important is the *build_phase* and *connection_phase* task.
The function *build_phase* shows how to use the reimplemented monitor with the UVM configuration database. Function *connect_phase* shows how to connect a low level monitor to a high level monitor.

.. code-block:: systemverilog

    class byte_array_mfb_monitor extends byte_array::monitor;
        ...
        virtual function void write(ll_transaction tr);
            // start of hl transaction
            if (tr.sof) begin
                fifo_data.delete();
                item = ll_transaction::type_id::create("item");
            end
            for (int unsigned it = 0; it < DATA_WIDTH; it++) begin
                fifo_data.push_back(tr.data[(it +1)*8-1 -: 8]);
            end
            // end of hl transaction
            if (tr.eof) begin
               item.data = fifo_data
               analysis_port.write(item);
            end
        endfunction
        ...
    endclass


Configuration object
====================

An enviroment create configuration object for his subenviroments or containing agents.
Folowing example shows how to create two configuration objects for agents which are instaintiate in current environment.

.. code-block:: systemverilog

    class env extends uvm_env
        ...
        function void build_phase(uvm_phase phase);
            byte_array_cfg m_byte_array_cfg;
            mfb_cfg        m_mfb_cfg;
            uvm_config_db#(byte_array_mfb_cfg)::get(this, "", "m_config", m_config);
            //save config object for subcomponent
            m_byte_array_cfg = new();
            m_byte_array_cfg.active = m_config.active;
            uvm_config_db#(byte_array_cfg)::set(this, "m_byte_array_agent", "m_config", m_byte_array_cfg);
            m_mfb_cfg = new();
            m_mfb_cfg.active   = m_config.active;
            m_mfb_cfg.vif_name = m_config.vif_name;
            uvm_config_db#(mfb_cfg)::set(this, "m_mfb_agent", "m_config", m_mfb_cfg);
            //create subcomponent
            m_byte_array = byte_array::type_id::create("m_byte_array", this);
            m_mfb_agent  = mfb_agent::type_id::create("m_mfb_agent", this);
        endfunction
        ...
    endclass


.. image:: ./docs/cofiguration_object.svg
    :align: center
    :alt: configuration object

Sequence library
====================

It is recommended to use a sequence library as a lower sequnece. It is going to have better coverage.

.. code-block:: systemverilog

    class sequence_library extends uvm_sequence_library;
       `uvm_object_utils(byte_array_mfb::sequence_library)
       `uvm_sequence_library_utils(byte_array_mfb::sequence_library)
        function new(string name = "");
            super.new(name)
            init_sequence_library();
        endfunction

        virtual function init_sequence();
            //run only this sequence
            this.add_sequence(test::sequence_packet_small::get_type());
            this.add_sequence(test::sequence_packet_mid::get_type());
            this.add_sequence(test::sequence_packet_rand_spaces::get_type());
            this.add_sequence(test::sequence_packet_constant::get_type());
            this.add_sequence(test::sequence_packet_increment::get_type());
            this.add_sequence(test::sequence_packet_large::get_type());
       endfunction
    endclass


Run of the specific sequence
============================

This example shows how to run a specific sequence on lower sequencer in environment from test.

create new sequence_library

.. code-block:: systemverilog

    class sequence_lib extends byte_array_mfb::sequence_library;
       `uvm_object_utils(test::sequence_lib)
       `uvm_sequence_library_utils(test::sequence_lib)
        function new(string name = "");
            super.new(name)
            init_sequence_library();
        endfunction

        virtual function init_sequence();
            //run only this sequence
            this.add_sequence(test::sequence_packet_large::get_type());
       endfunction
    endclass


Code below shows how to change the sequence library using UVM abstract factory.

.. code-block:: systemverilog

    class test extends uvm_test;
        ...
        function void build_phase(uvm_phase phase);
            //change implementation
            byte_array_mfb::sequence_lib::type_id::set_inst_override(sequence_lib::get_type(), {this.get_full_name() ,".m_env.rx_agent*"});
            ...
            //create environment with change
            m_env = component::env::type_id::create("m_env", this);
        endfunction
    endclass


Common environment
###################################

Environment (uvm_env) puts together agents, subenvironments and others components into a logical unit.
Common use of the environmet is connect high level agent with low level agent. Picture below shows
environment with two agents, one environment and one virtual sequencer.

.. image:: ./docs/enviroment.svg
    :align: center
    :alt: environment

Virtual sequencer
====================

Virtual sequencer connects all highest level sequencers into one sequencer. On that sequencer runs a virtual seqeunce.
If the environment contains other environment like on previous picture, virtual sequencer consist only of highest sequencer from subenvironment.

.. image:: ./docs/virtual_sequencer.svg
    :align: center
    :alt: virtual sequencer


.. code-block:: systemverilog

    class sequencer extends uvm_sequencer;
        `uvm_component_utils(env::sequencer)

        mfb::sequencer m_mfb_sequencer;
        mvb::sequencer m_mvb_sequencer;
        config::sequencer m_config_sequencer; 

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction
    endclass


.. code-block:: systemverilog

    class sequence_simple extends uvm_sequence;
        `uvm_object_param_utils(env::sequence_simple)
        `uvm_declare_p_sequencer( env::sequencer )

        //sequence define
        mfb::sequence_simple mfb_sequence;
        mvm::sequence_simple mvb_sequence;
        config::sequence_simple config_sequence;

        function new (string name = "");
            super.new(name);
        endfunction

        task body();
            fork
                `uvm_do_on(mfb_sequence, p_sequencer.m_mfb_sequencer);
                `uvm_do_on(mvb_sequence, p_sequencer.m_mvb_sequencer);
                `uvm_do_on(config_sequence, p_sequencer.m_config_sequencer);
            join
        endtask
    endclass


Virtual sequence and synchronization
====================================


Scoreboard
====================

Scoreboard simply connects the DUT and compares transaction expected from a model and transaction gained from the DUT.
It is appropriate to implement the *report_phase* which prints some statistics at the end of simulation to inform the user how depth verification was.
It is good practice to write uniform text such as *VERIFICATION SUCCESS* when verification ends successfully, which can be useful in some automatic testing tools such as *Jenkins*.

Verification should check if the design haven't stuck.
For example the DUT can set all *rdy* signals to zero and don't change them until the end of verification.
This means that no packet goes through design and it should be reported by verification.

Model should be implemented in a indepedent class. Example below shows how should Scoreboard and Model cooperate. Scoreboard only check equality of each transaction.
if transaction isn't same then the socreboard print error message through macro UVM_error.

.. note::
    macro UVM_error dosn't stop verificatin. On end of simulation the Scoreboard have to check if some errors ocurre in verification.


.. image:: ./docs/scoreboard.svg
    :align: center
    :alt: scoreboard


.. code-block:: systemverilog

    class scoreboard uvm_scoreboard;
        `uvm_component_utils(env::scoreboard)
        //CONNECT DUT
        uvm_analysis_export #(packet::sequence_item) analysis_export_rx;
        uvm_analysis_export #(packet::sequence_item) analysis_export_tx;
        //output fifos
        uvm_tlm_analysis_fifo #(packet::sequence_item) model_fifo;
        uvm_tlm_analysis_fifo #(packet::sequence_item) dut_fifo;
        //models
        model m_model;

        function new(string name, uvm_coponent parent = null);
          super.new(name, parent);
          analysis_export_rx = new("analysis_imp_rx", this);
          analysis_export_tx = new("analysis_imp_tx", this);
          model_fifo = new("model_fifo", this);
          dut_fifo   = new("dut_fifo", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            analysis_export_rx.connect(m_model.input.anlysis_export);
            analysis_export_tx.connect(dut_fifo.analysis_export);
            m_model.output.connect(model_fifo.analysis_export);
        endfunction

        task run_phase();
            forever begin
                model_fifo.get(tr_model);
                dut_fifo.get(tr_dut);
                if (tr_model.compare(tr_dut) == 0) begin
                    `uvm_error(...);
                end
            end
        endtask

        virtual function void report_phase(uvm_phase phase);
            if (this.success() && dut_output.used() == 0 && model_output.used() ==0) begin
                `uvm_info(get_type_name(), "\n\t---------------------------------------\n\t----     VERIFICATION SUCCESS      ----\n\t---------------------------------------", UVM_NONE)
            end else begin
                `uvm_info(get_type_name(), "\n\t---------------------------------------\n\t----     VERIFICATION FAIL      ----\n\t---------------------------------------", UVM_NONE)
            end
        endfunction
    endclass


Request response Agents
###################################

Some agents may require bidirectional comunications.
For this purpose the UVM has the Request response mechanism.

For example the read request on MI has two transaction.
The first transaction is master and the second transaction is slave.

.. image:: ./docs/MI_agent.svg
    :align: center
    :alt: question response


Reset
###################################

One possible solution to the problem when reset is generated in the middle of verification (not only at the start of verification) is to use the wait task to wait for all required
inputs. An example is shown below showing this type of solution.
The problem that can occur is if the process read input A and wait for input B then a reset happens and all data should be flush. After the reset process receives
input B and model connects the wrong data. Input A receives before reset with input B after reset. This solution can be made as in scoreboard as in model.
For more info see reset agent documentation.

Scoreboard
====================

.. code-block:: systemverilog

    class scoreboard uvm_scoreboard;
        `uvm_component_utils(env::scoreboard)
        uvm_analysis_imp_reset#(reset::sequence_item, scoreboard) analysis_imp_reset;
        model m_model;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            analysis_imp_reset = new("analysis_imp_reset", this);
        endfunction

        function void write_reset(reset::sequence_item tr);
            //RESET
            dut_fifo.flush();
            model_fifo.flush();
            m_regmodel.reset();
            m_model.reset();
        endfunction

        task run_phase(uvm_phase phase);
            ...
            forever begin
                //wait for DUT and model transactions. Reset can erase all unfinished transactions
                wait(dut_fifo.used() != 0 && model_fifo.used() != 0);

                compared++;
                if (dut_tr.compare(model_tr) == 0) begin
                    `uvm_error(...);
                end
            end
        endtask
    endclass


Coverage
###################################

Coverage is one of important metrics for checking verification status. Coverage can tell if the verification of design is done properly.
Every verification should check if coverage is high enought if not verification designer should explain why is not.

.. code-block:: systemverilog

    class output_cover #(OUTPUTS) extends uvm_subscriber#(seqeunce_item);
        `uvm_component_param_utils(packet_port_env::output_cover #(OUTPUTS))
        sequence_item item;

        covergroup cov_packet;
            items_size : coverpoint item.packet.data {
                bins num[512] = {[0:2**16-1]};
                illegal_bins others = default;
            }
            items_port : coverpoint item.port {
                bins num[OUTPUTS] = {[0:OUTPUTS-1]};
                illegal_bins others = default;
            }
            cross items_size, items_port;
        endgroup
        ...

        function void write(sequence_item tr);
            item = tr;
            cov_packet.sample();
        endfunction
    endclass


Functional coverage
====================

Every model should contains functional coverage to check if all of the funcionality was tested.
Functional coverage can be measured in model.

.. code-block:: systemverilog

    class coverage_base extends  uvm_subscriber#(sequence_item);
        sequence_item item;
        covergroup m_cov;
            ones: coverpoint $countones(item.mash) {
                bins ones[] = {[0:20]};
            }
        endgroup

        function new (string name, uvm_component parent = null);
            super.new(name, parent);
            m_cov = new();
        endfunction

        function void write(sequence_item t);
            item = t;
            m_cov.sample();
        endfunction
    endclass


Code coverage
====================

Code coverage represents how many lines, conditional jumps and expression the test checks.

A simple metric is mostly generated by verification tool.
In the OFM verification environment can be set up by adding *set SIM_FLAGS(CODE_COVERAGE) "true"* into file *top_level.fdo*.

Generating coverage reports
~~~~~~~~~~~~~~~~~~~~~~~~~~~

ModelSim can generate coverage reports into HTML:

* *coverage report -html -output cov_html -instance=/testbench/DUT_U -source -details -assert -directive -cvg -code bcefst -verbose -threshL 50 -threshH 90*

Merge more report from one simulation. Next commands is for our multiver script.
After every simulation is coverage save into actual.ucdb. Next command merge coverage from
actual simulation with all earlest simulation. Last command generate html output.

* *coverage save -assert -directive -cvg -code bcefst -verbose actual.ucdb-*
* *vcover merge final.ucdb final.ucdb actual.ucdb*
* *vcover report -html -output cov_html -instance=/testbench/DUT_U -source -details -assert -directive -cvg -code bcefst -verbose -threshL 50 -threshH 90 final.ucdb*


Verification example
###################################

Let say we have component MFB splitter which divide MFB stream into N output streams. With every incoming packet to mfb, also came information about output port.
Output ports is send on MVB interface. For simplified verification MVB interface is not aligned to MFB. Use method FIFO. It is only depend on ordering MFB and MVB streams.

The image show block connection of such verification.

.. image:: ./docs/mfb_splitter.svg
    :align: center
    :alt: Verification connection


Byte_array_port environment
===========================

Environment is used for grouping byte_array and port. Advantage of this solution is generating data for MVB and MFB in one roll.

.. code-block:: systemverilog

    class sequence_item extend uvm_sequence_item;
        `uvm_object_utils(byte_array_port_env::sequnece_item)
        rand byte_array::sequence_item packet;
        rand int unsigned              port;
        ...
    endclass


Because is required to divide high level sequence, we cannot use pointer directly to high level sequencer. So we use driver to divide sequence into two piece

.. code-block:: systemverilog

    class driver extends uvm_driver#(sequence_item);
      `uvm_component_utils(byte_array_port_env::drivere)
       mailbox #(byte_array::sequence_item) msg_byte_array;
       mailbox #(int unsigned)              msg_port;

       function new(string name, uvm_component parent = null);
           super.new(name, parent);
           msg_byte_array = new(10); //max 10 requests
           msg_port       = new(10);
       endfunction

       task run_phase(uvm_phase phase);
           byte_array::sequence_item tr_paket;
           int unsigned              tr_port;
           forever begin
               seq_item_port.get_next_item(req);
               tr_paket = req.paket.clone();
               msg_byte_array.put(tr_paket);
               tr_port  = req.port;
               msg_port.put(tr_port);
               seq_item_port.item_done(req);
           end
       endtask
    endclass

Environment contains two sequences. One generate *byte_array::sequence_item*. Second generate *mvb::sequence_item*.

.. code-block:: systemverilog

    class sequence_byte_array extends uvm_sequnece#(byte_array::sequence_item);
        `uvm_object_utils(byte_array_port_env::sequence_byte_array)
         mailbox #(byte_array::sequence_item) in_data;
         ...
         taks body();
             forever begin
                 in_data.get(req);
                 start_item(req);
                 finish_item(req);
             end
         endtaks
    endclass


.. code-block:: systemverilog

    class sequence_mvb extends uvm_sequnece#(mvb::sequence_item);
        `uvm_object_utils(byte_array_port_env::sequence_mvb)
         mailbox #(int unsigned) in_data;
         ...
         taks body();
             req = mvb::sequence_item::type_id::create("byte_array_port_env::mvb");
             int unsigned mvb_valid_items;
             forever begin
                 bit rdy = 0;
                 start_item(req);
                 req.randomize();
                 for (int unsigned it = 0; it < REGIONS; it++) begin
                      if (req.vld[it] == 1 && in_data.num() != 0) begin
                          rdy = 1;
                          in_data.get(req.data[it]);
                      end else begin
                           req.data[it] = 'x
                      end
                 end
                 req.rdy &= rdy;
                 finish_item(req);
             end
         endtaks
    endclass


Next code shows how to put all together.

.. code-block:: systemverilog

    class env extends uvm_env;
        `uvm_component_utils(byte_array_port_env::env)
        sequencer m_sequencer;
        driver    m_driver;
        monitor   m_monitor;
        //low level agents
        byte_array_mfb::agent byte_array_agent;
        mvb::agent            mvb_agent;
        ...
        task run_phase(uvm_phase phase);
           sequence_byte_array seq_byte_array;
           sequence_mvb        seq_mvb;
           seq_byte_array = sequence_byte_array::type_id::create("sequence_byte_array");
           seq_byte_array.in_data = m_driver.msg_byte_array;
           seq_mvb        = sequence_mvb::type_id::create("sequence_mvb");
           seq_mvb.in_data = m_driver.msg_mvb;
           fork
               seq_byte_array.start(byte_array_agent.m_sequencer);
               seq_mvb.start(mvb_agent.m_sequencer);
           join
        endtask
    endclass


Model
======================

Inputs and outputs of the models are implemented by the transaction level model - in UVM are used the *uvm_analysis_*, *uvm_tm_analysis_* macros. Model have the same outputs and inputs as DUT.
This aproach has been chosen because the models can be easily connected together to create another model contanaining more smlaller models.

Sometimes is required to pass meta-informations through models. For example when we have one model composite from others models and one of the internal models can discard some data. Then we cannot
add some meta information such as time when packet enter to DUT to count delay of DUT. This information can be used to measure maximum delay of DUT.
We haven't yet found out how to aproach this problem. One simple solution is by reimplementing all internal models but this aproach is quite time consuming.


.. code-block:: systemverilog

    class model#(PORTS) extends uvm_component;
        `uvm_componet_param_utils(packet_splitter::model#(PORTS))
        uvm_tlm_analysis_fifo #(byte_array_port_env::sequence_item, model) analysis_imp_rx;
        uvm_analysis_port     #(byte_array::sequence_item)                 analysis_port_tx[PORTS];

        function new (string name, uvm_component parent = null);
            super.new(name, parent);
            analysis_imp_rx = new ("analysis_imp_rx", this);
            for (int unsigned it = 0; it < PORTS; it++) begin
                string it_num;
                it_num.itoa(it);
                analysis_port_tx[it] = new({"sc_output_", it_num}, this);
            end
        endfunction

        task run_phase(uvm_phase);
            byte_array_port_env::sequence_item tr;
            forever begin
                analysis_imp_rx.get(tr);
                //model write packet to output
                analysis_port_tx[tr.port].write(tr.packet);
            end
        endtask
    endclass


Scoreboard
======================

.. code-block:: systemverilog

    class soreboard #(PORTS, REGIONS) extens uvm_scoreboard;
        `uvm_componet_param_utils(packet_splitter::scoreboard#(PORTS, REGIONS))
        //INPUT FROM DUT
        uvm_analysis_export#(byte_array_port_env::sequence_item) analysis_export_rx_packet;
        uvm_analysis_export#(byte_array::sequence_item)          analysis_export_tx_packet[PORTS];
        //OUTPUT TO SCOREBOARD
        uvm_tlm_analysis_fifo#(byte_array::sequnece_item) dut_output[PORTS];
        uvm_tlm_analysis_fifo#(byte_array::sequnece_item) model_output[PORTS];
        //internal components
        packet_splitter::model #(PORTS) m_model;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            analysis_export_rx_packet = new ("analysis_export_rx_packet", this);
            for (int unsigned it = 0; it < PORTS; it++) begin
                string it_num;
                it_num.itoa(it);
                analysis_export_tx_packet[it] = new({"analysis_export_tx_packet_", it_num}, this);
                dut_output[it]                = new({"dut_output_", it_num}, this);
                model_output[it]              = new({"model_output_", it_num}, this);
            end
        endfunction

        function void build_phase(uvm_phase phase);
            m_model = model::packet_splitter#(PORTS)::type_id::create("m_model", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            analysis_export_rx_packet.connect(m_model.analysis_imp_rx.analysis_export);
            for (int unsigned it = 0; it < PORTS; it++) begin
                 analysis_export_tx_packet[it].connect(dut_output[it].analysis_export);
                 m_model.analysis_port_tx[it].connect(model_output[it].analysis_export);
            end
        endfunction

        task run_phase_port(uvm_phase phase, intunsigned port);
            forever begin
                dut_output.get(tr_out);
                model_output.get(tr_model);
                if (tr_out.compare(tr_model) != 1)
                    `uvm_error(...);
            end
        end

        task run_phase(uvm_phase phase);
             fork...
                run_phase_port(phase, it);
             join
        endtask

        function void report_phase(uvm_phase phase);
            //print statistics
            m_model.display();
            if (this.sucess() && dut_output.used() == 0 && model_output.used() == 0) begin
                `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
                `uvm_info(get_type_name(), "----     VERIFICATION SUCCESS      ----", UVM_NONE)
                `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
            end else begin
                `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
                `uvm_info(get_type_name(), "----     VERIFICATION FAIL         ----", UVM_NONE)
                `uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
            end
        endfunction
    endclass


Test environment
======================

After creating model and scoreboard we assembly test environment *env*. We need environment *byte_array_port* which we created earlier and environment *byte_array_mfb*
which is store in *OMF:comp/uvm/byte_array_mfb*. It is requred to put correct path to file *Modules.tcl*


.. code-block:: systemverilog

    class env#(PORTS, REGIONS) extends uvm_env;
        `uvm_componet_param_utils(packet_splitter::env#(PORTS, REGIONS))
        //rx agents
        byte_array_port_env::env             rx_env;
        //tx agent
        byte_aray_mfb::tx_env_base#(REGIONS) tx_env[PORTS];
        //scoreboard
        scoreboard#(PORTS, REGIONS) sc;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            rx_env = byte_array_port_env::env::type_id::create("rx_env", this);
            for (int unsigned it = 0; it < PORTS; it++) begin
                string it_num;
                it_num.itoa(it);
                tx_env[it] = byte_aray_mfb::tx_env_base#(REGIONS)::type_id::create({"tx_env_", it_num}, this);
            end
            sc = scoreboard#(PORTS, REGIONS)::type_id::create("sc", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            rx_env.analysis_port.connect(sc.analysis_export_rx_packet);
            for (int unsigned it = 0; it < PORTS; it++) begin
                tx_env[it].m_byte_array.analysis_port(sc.analysis_export_tx_packet[it]);
            end
        endfunction
    endclass


Test
======================

Test runs the highest level seqeunce and create specific adjustment to verification environment. For some tests we want to generate full speed traffic for mfb without any
interframe and between frame spaces. This adjustmens is add by UVM abstract factory. If you wish to see example looking for *sequence library* on this page.

example of full speed mfb sequence

.. code-block:: systemverilog

    class sequence_rx_rdy extends uvm_sequencex(mfb::sequence_item)
        `uvm_object_utils(test::sequence_rx_rdy)

        function new(string name);
            super.new(name);
        endfunction

        task body();
             req = mfb::sequence_item::type_id::create();
             forever begin
                `uvm_do_with (req, {rdy == 1});
             end
        endtask
    endclass


Test example

.. code-block:: systemverilog

    class base extends uvm_test
        `uvm_componet_utils(test::base)
        packet_splitter::env_main#(8, 2) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            m_env = packet_splitter::env_main#(8,2)::type_id::create("m_env", this);
        endfunction

        task run_phase(uvm_phase phase);
             test::sequence_rx     seq_rx_pacet;
             test::sequence_tx_rdy seq_tx_rdy;
             phase.raise_objection(this);
             fork
                `uvm_do(seq_rx_packet, m_env.rx_env.m_sequencer);
                `uvm_do(seq_tx_rdy,    m_env.tx_env.m_sequencer);
             join_any
             phase.drop_objection(this);
        endtask
    endclass


Properties
======================

Properties contains interface protocols rules which have to DUT keep. Also it can contain some other DUT properties.

.. code-block:: systemverilog

    modules mfb_splitter_properties #(OUTPUTS) (logic CLK, reset_if RESET, mfb_if RX_MFB, mvb_if RX_MFB, mfb_if TX_MFB[OUTPUTS]);
        mfb_propeties (
             .CLK   (CLK),
             .RESET (RESET),
             .MFB   (RX_MFB)
          );

        mvb_properties (
             .CLK   (CLK),
             .RESET (RESET),
             .MVB   (RX_MVB)
        );
        // you can add some properties if you want.
    endmodule


testbench
======================

After the run_test command is required to put command $stop(). If you want to stop quitting ModelSim after drop_objection, you must
set the variable finish_on_completion to zero. If you set the variable finish_on_completion to zero, verification doesn't have to stop.
This problem is fixed by putting command $stop() after command run_test(); If you wish to generate coverage you have to set
set variable finis_on_completion to zero.

.. code-block:: systemverilog

    module testbench #(OUTPUTS);
        logic CLK = 0;

        reset_if                                               rst(CLK);
        mvb_if #(REGIONS, MVB_ITEM_WIDTH)                      rx_mvb(CLK);
        mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH) rx_mfb(CLK);
        mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH) tx_mfb[OUTPUTS](CLK);

        // create clock
        always #(CLK_PERIOD) CLK = ~CLK;

        // Start of tests
        initial begin
            uvm_root m_root;
            virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH) v_tx_mfb;
            v_tx_mfb = tx_mfb;
            // Configuration TX
            for (int i = 0; i < OUTPUTS; i++ ) begin
                string i_string;
                i_string.itoa(i);
                uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH))::set(null, "", {"OUTPUT_MFB_",i_string}, v_mfb_tx[i]);
            end
            // save pointer to interface into configuration database
            uvm_config_db#(virtual mfb_if #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH))::set(null, "", "INPUT_MFB", rx_mfb);
            uvm_config_db#(virtual mvb_if #(REGIONS, MVB_ITEM_WIDTH))::set(null, "", "INPUT_MVB", rx_mfb);
            uvm_config_db#(virtual reset_if)::set(null, "", "RESET", rst);

            m_root = uvm_root::get();           //get root component
            m_root.finish_on_completion = 0;    //now finish on end. required stop command after run_test
            //stop reporting ILEGALNAME when sequence in sequence library have been started
            m_root.set_report_id_action_hier("ILLEGALNAME",UVM_NO_ACTION);

            run_test();
            $stop(2);
        end

        // DUT modul
        DUT #(OUTPUTS) DUT_U (
          .CLK    (CLK),
          .RESET  (rst),
          .RX_MFB (rx_mfb),
          .RX_MVB (rx_mvb),
          .TX_MFB (mfb)
        );

        // check of properties
        MFB_SPLITTER_PROPERTIES #(OUTPUTS) PRT (
          .CLK   (CLK),
          .RESET  (rst),
          .RX_MFB (rx_mfb),
          .RX_MVB (rx_mvb),
          .TX_MFB (mfb)
        );
    endmodule


NOTES
###################################

UVM_error vs UVM_fatal
======================

Difference between macros UVM_error and UVM_fatal is in meaning.
Macro UVM_fatal represents error in verification environment. For example when agent cannot find an interface.

The macro UVM_error should be used for reporting errors in DUT, for example when the output transaction doesn't match expected transaction.

For better readability messages written by macro follow folowing rules:
#. On start of string print new line with tabulator *"\n\ttext"*
#. After a new line is required put one or more tabulator depend on indentation.
#. Don't write new line on end of text. UVM macros automatically add new line on the end of string.


Parametrized object
=====================

If you need a parametrised uvm_object or uvm_component then use registration macros *uvm_component_param_utils* and *uvm_object_param_utils*.
Parametrised object can be required when some interface has parametrised signal width.

.. code-block:: systemverilog

    class non_parametrized_class extends uvm_object;
        `uvm_object_utils#(pkg::non_parametrized_class);

         ...
    endclass

.. code-block:: systemverilog

    class parametrized_class#(PARAM) extends uvm_object;
        `uvm_object_param_utils#(pkg::non_parametrized_class#(PARAM));

        logic [PARAM-1:0] val;
         ...
    endclass



Synchronization
=====================

For synchronization in the UVM exists the uvm_event class. The uvm_event class provides more functionality such as standard barier in SystemVerilog.
Also there is a uvm_pool which provides access to uvm_barier using name.


OFM verification environment
###################################


When you create new agent you can inspirate yourself by `MVB agent <https://gitlab.liberouter.org/ndk/ofm/-/tree/devel/comp/uvm/mfb>`_.
All classes which are related to one agent or environment should be placed in one directory.
All files are included by a package.
In this directory should exists a Modules.tcl file which includes pkg.sv, interface.sv if required and all required packages.
If the interface is bidirectional then all files with uvm_component should contain two classes: agent_rx and agent_tx.
See the MI interface as an example for bidirectional and pipelined interface.
Also the slave side has to be able to respond in the same clock cycle as request occurs (this is not implemented).

.. image:: ./docs/interface_direction.svg
    :align: center
    :alt: interface direction


Modules.tcl
=====================

This file is written in TCL language.
The file contains required files and required dependencies for package.
Following command adds a package which will be compiled first.
Common use can add math_pkg.sv which contain common mathematical function.

.. code-block:: tcl

    lappend PACKAGES "$ENTITY_BASE/math_pack.vhd"

Folowing command add two required commponent *SH_REG* and *FIFOX*. Component *SH_REG* is in directory *OFM_PATH/comp/base/shreg/sh_reg_base* and load architecture *FULL*.

.. code-block:: tcl

    lappend COMPONETS [ list "SH_REG"      $OFM_PATH/comp/base/shreg/sh_reg_base       "FULL" ]
    lappend COMPONETS [ list "FIFOX"       $OFM_PATH/comp/base/fifo/fifox              "FULL" ]

Two file *./arch.vhd* and *ent.vhd* contain VHDL design. Following command load this two files.

.. code-block:: tcl

    lappend MOD "$ENTITY_BASE/arch.vhd"
    lappend MOD "$ENTITY_BASE/ent.vhd"


Main .fdo script for running the verification
=================================================

This file is typically named top_level.fdo.
Basically contains the COMPONENT variable, which hold typically two items:
the first component is the verified design (DUT), and the second component is the verification environment.

.. code-block:: tcl

     lappend COMPONETS [list "DUT"  $DUT_BASE  "FULL"]
     lappend COMPONETS [list "VER"  $VER_BASE  "FULL"]


You can suppress warnings printed by the numeric_std or the std_logic_arith library.

.. note::
  Using of the std_logic_arith is discouraged.


.. code-block:: tcl

    #Suppress warnings from arith library
    puts "Numeric Std Warnings - Disabled"
    set NumericStdNoWarnings 1
    puts "Std Arith Warnings - Disabled"
    set StdArithNoWarnings 1

Folowing command add some extra parametr to vsim. last parametr *+UVM_MAX_QUIT_COUNT=X* stop verification after *X* UVM_errors occure.

.. code-block:: tcl

   set SIM_FLAGS(EXTRA_VFLAGS) "+UVM_TESTNAME=test::base -uvmcontrol=all +UVM_MAX_QUIT_COUNT=1"


This command loads the OFM build environment, compiles the sources for simulation and runs the simulation with vsim:

.. code-block:: tcl

    source "$FIRMWARE_BASE/build/Modelsim.inc.fdo"

Now you can run the verification by passing the .fdo file name to the `vsim -do` command. You can also run the verification in command line (without GUI) with the switch -c:

.. code-block:: bash

    vsim -do top_level.fdo -c

