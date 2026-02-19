.. howto-extend_ver.rst: This document expands the simple howto.
.. Copyright (C) 2025 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. UVM howto
.. _uvm_howto_extend_verification:


********************************
UVM HOWTO - Upgrade verification
********************************

This chapter describes how to improve a verification environment once you have
a basic one running. It builds on the flow from the :ref:`uvm_howto_intro` and
the environment you create in the :ref:`uvm_howto_first_ver` (test, environment,
UVCs, model, scoreboard). If you are new to UVM in this repository, read the
intro first for the big picture.

==================
Add Register model
==================

The register model simplifies organisation and working with registers in the verification environment.
This FIFO component doesn't have any accessible registers from outside. Therefore, create a simple
register in *testbench.sv*. So it would be possible to create and demonstrate a simple register model.
This chapter is only about a demonstration register model.

In this example we create one simple register in the testbench to demonstrate how the register model works.
We create register which enable output FIFO. Register disable reading from the FIFO.
Only the "valid" signal of the output (tx_src_rdy) depends on the register's value.
Create the testbench which enables output depending on the value stored in the register. Writing to the register
is going to be done through the register model. For accessing registers through the register model
the NDK environment uses the MI interface.


.. code-block:: systemverilog
   :caption: testbench.sv

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import uvm_generic::*;

    module testbench;
        // Create test with parameters (Register in factory)
        typedef test::base#(uvm_generic::DATA_WIDTH) base;

        // Create clock
        logic CLK = 0;
        always #(CLK_PERIOD/2) CLK = ~CLK;

        reset_if reset (CLK);
        mvb_if #(1, DATA_WIDTH)     mvb_rx    (CLK);
        mvb_if #(1, DATA_WIDTH)     mvb_tx    (CLK);

        mi_if  #(32, 32)            config    (CLK);


       initial begin
            uvm_root m_root;

            // REGISTER INTERFACE INTO DATABASE
            uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
            uvm_config_db #(virtual mvb_if #(1, DATA_WIDTH))    ::set(null, "", "vif_mvb_rx",     mvb_rx    );
            uvm_config_db #(virtual mvb_if #(1, DATA_WIDTH))    ::set(null, "", "vif_mvb_tx",     mvb_tx    );
            uvm_config_db #(virtual mi_if  #(32, 32))           ::set(null, "", "vif_mi",         config    );

            // STOP on end of simulation and dont print message ILLEGALNAME
            m_root = uvm_root::get();
            m_root.finish_on_completion = 0;
            m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

            // DONT RECORD TRANSACTIONS
            uvm_config_db #(int)            ::set(null, "", "recording_detail", 0);
            uvm_config_db #(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

            // RUN TESTS
            run_test();
            // STOP ON END OF SIMULATION
            $stop(2);
        end

        //INSTANTIATE DUT
        logic full;
        logic empty;
        logic rd;
        FIFOX #(
            .DATA_WIDTH          (uvm_generic::DATA_WIDTH         ),
            .ITEMS               (uvm_generic::ITEMS              ),
            .RAM_TYPE            (uvm_generic::RAM_TYPE           ),
            .DEVICE              (uvm_generic::DEVICE             ),
            .ALMOST_FULL_OFFSET  (uvm_generic::ALMOST_FULL_OFFSET ),
            .ALMOST_EMPTY_OFFSET (uvm_generic::ALMOST_EMPTY_OFFSET),
            .FAKE_FIFO           (uvm_generic::FAKE_FIFO          )
        ) VHDL_DUT_U (

            .CLK   (CLK),
            .RESET (RST),

            .DI     (mvb_rx.DATA),
            .WR     (mvb_rx.SRC_RDY & mvb_rx.VLD[0]),
            .FULL   (full),
            .AFULL  (),
            .STATUS (),

            .DO     (mvb_tx.DATA   ),
            .RD     (rd),
            .EMPTY  (empty         ),
            .AEMPTY ()

        );


        // CREATE REGISTER
        logic enable = '0;
        always @(posedge CLK)
        begin
            if(config.WR == 1'b0 and config.ADDR == '0) begin
                enable <= config.DWR[0];
            end
        end

        assign config.ARDY    = config.WR | config.RD;
        assign config.DRDY    = config.RD;
        assign config.DRD[0]  = enable;

        assign mvb_rx.DST_RDY = ~full;
        // Stop read from the fifo when enable register is disabled
        assign rd             = mvb_tx.DST_RDY & ~empty;
        assign mvb_tx.SRC_RDY = ~empty & enable;
        assign mvb_tx.VLD     = '1;
    endmodule


The environment modification requires adding the register model and connecting to the MI interface.

.. code-block:: systemverilog
   :caption: env/env.sv

    class env #(
        int unsigned DATA_WIDTH
    ) extends uvm_env;
        `uvm_component_param_utils(uvm_fifox::env #(DATA_WIDTH));

        // Virtual sequencer
        sequencer #(DATA_WIDTH) m_sequencer;

        // RESET interface
        protected uvm_reset::agent m_reset;
        // RX environments
        protected uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH) m_rx;
        // TX environments
        protected uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH) m_tx;

        // Register model
        protected uvm_mi::regmodel#(regmodel, 32, 32) m_regmodel;

        //Model
        uvm_fifox::model #(DATA_WIDTH) m_model;
        // Scoreboard
        protected scoreboard #(DATA_WIDTH) m_sc;

        // Constructor
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        // Create base components of environment.
        function void build_phase(uvm_phase phase);
            uvm_mi::regmodel_config  cfg_mi;
            uvm_reset::config_item m_cfg_reset;
            uvm_logic_vector_mvb::config_item m_cfg_rx;
            uvm_logic_vector_mvb::config_item m_cfg_tx;

            //Call parents function build_phase
            super.build_phase(phase);

            //Create reset environment
            m_cfg_reset                = new;
            m_cfg_reset.active         = UVM_ACTIVE;   // Activly driven environment
            // interface register name has to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_reset.interface_name = "vif_reset";
            uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_cfg_reset);
            // Creation of the reset
            m_reset = uvm_reset::agent::type_id::create("m_reset", this)

            // Configuration of the m_env_mvb_rx
            m_cfg_rx                = new;
            m_cfg_rx.active         = UVM_ACTIVE;
            // interface register name has to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_rx.interface_name = "vif_mvb_rx";
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_rx", "m_config", m_cfg_rx);
            // Creation of the m_env_mvb_rx
            m_env_mvb_rx = uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_rx", this);

            // Configuration of the m_env_mvb_tx
            m_cfg_tx                = new;
            m_cfg_tx.active         = UVM_ACTIVE;
            // interface register name has to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_tx.interface_name = "vif_mvb_tx";
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_tx", "m_config", m_cfg_tx);
            // Creation of the m_env_mvb_tx
            m_env_mvb_tx = uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_tx", this);

            cfg_mi  = new();
            cfg_mi.addr_base            = 'h0;
            cfg_mi.agent.active         = UVM_ACTIVE;
            cfg_mi.agent.interface_name = "vif_mi";
            uvm_config_db#(uvm_mi::regmodel_config)::set(this, "m_regmodel", "m_config", cfg_mi);
            m_regmodel = uvm_mi::regmodel#(regmodel, 32, 32)::type_id::create("m_regmodel", this);

            m_sc = scoreboard #(DATA_WIDTH)::type_id::create("m_sc", this);
            m_model = uvm_fifox::model #(DATA_WIDTH)::type_id::create("m_model", this);
        endfunction

        // Connect agent's ports with ports from scoreboard.
        function void connect_phase(uvm_phase phase);
            // Connection of the reset
            m_reset.sync_connect(m_rx.reset_sync);

            // Connection to Model
            m_rx.analysis_port.connect(m_model.m_rx.analysis_export);

            // Connect to Scoreboard
            m_model.m_tx.connect(m_sc.cmp.analysis_imp_model);

            // Connect sequencer
            m_sequencer.m_reset = m_reset.m_sequencer;
            m_sequencer.m_rx    = m_rx.m_sequencer;
            m_sequencer.m_regmodel = m_regmodel.m_regmodel;
        endfunction
    endclass


The Register model contains one register, which enables FIFO functionality.
Write 1'b1 to enable the FIFO. Write 1'b0 to disable the FIFO. *uvm_reg_field* represents a register.
Create a register sequence and add the register model to the sequencer.

.. code-block:: systemverilog
   :caption: env/regmodel.sv

    // create control register
    class reg_control extends uvm_reg;
        `uvm_object_utils(uvm_fifox::reg_control)

        // field inside register.
        rand uvm_reg_field enable;

        function new(string name = "reg_status");
            super.new(name, 1, UVM_NO_COVERAGE);
        endfunction

        virtual function void build();
            // Create fields
            enable = uvm_reg_field::type_id::create("enable");

            // Configure
            // https://verificationacademy.com/verification-methodology-reference/uvm/docs_1.1a/html/files/reg/uvm_reg_field-svh.html#uvm_reg_field.configure
            enable.configure( this, // Parent
                              1   , // Number of bits
                              0   , // LSB position. (position of first bit in register)
                              "RW", // Access
                              0   , // Volatility
                              0   , // Value on reset
                              1   , // Can the value be reset?
                              0   , // Can the value be randomized?
                              0     // Does the field occupy an entire byte lane?
                                   );
        endfunction
    endclass

    // register model
    class regmodel extends uvm_reg_block;
        `uvm_object_utils(uvm_fifox::regmodel)

        // registers in componnent
        reg_control ctrl;

        function new(string name = "reg_model");
            super.new(name, build_coverage(UVM_NO_COVERAGE));
        endfunction

        virtual function void set_frontdoor(uvm_reg_frontdoor frontdoor);
            uvm_reg_frontdoor c_frontdoor;
            $cast(c_frontdoor, frontdoor.clone());
            ctrl.set_frontdoor(c_frontdoor);
        endfunction

        virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);

            // Create register
            ctrl = reg_control::type_id::create("enable");
            ctrl.configure(this);
            ctrl.build();

            // Create map to register array
            this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
            // Put register to map  // REGISTER, register address, access right
            this.default_map.add_reg(ctrl, 'h0, "RW");

            // Lock model
            this.lock_model();
        endfunction
    endclass


.. code-block:: systemverilog
   :caption: env/reg_sequence.sv

    // Register sequence. Write 1 into enable register
    class reg_sequence extends uvm_sequence;
        `uvm_object_utils(uvm_fifox::reg_sequence)
        rand logic enabled;
        regmodel m_regmodel;

        function new (string name = "sequence_simple");
            super.new(name);
        endfunction

        task body();
            uvm_status_e   status;
            m_regmodel.ctrl.enable.write(status, 1'b1, .parent(this));
        endtask
    endclass


Add the register model into virtual sequencer to simplify run sequence.

.. code-block:: systemverilog
   :caption: env/sequencer.sv

    class sequencer#(
        int unsigned DATA_WIDTH
    ) uvm_sequencer;
        `uvm_component_param_utils(uvm_fifox::sequencer #(DATA_WIDTH))

        // reset sequencer
        uvm_reset::sequencer m_reset;
        // rx sequencer
        uvm_logic_vector::sequencer #(DATA_WIDTH)    m_rx;
        // the register model
        regmodel m_regmodel;

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction
    endclass


.. code-block:: systemverilog
   :caption: env/pkg.sv

    `define FIFOX_ENV_SV
    package uvm_fifox;
        `include "uvm_macros.svh"
        import uvm_pkg::*;

        `include "regmodel.sv"

        `include "sequencer.sv"
        `include "model.sv"
        `include "scoreboard.sv"
        `include "env.sv"

        `include "reg_sequence.sv"
    endpackage
    `endif


Enable the FIFO by executing the *reg_sequence* in the test.
*reg_sequence* writes 1'b1 to the enable register in the design.
Other sequences are executed after writing to the register.

.. code-block:: systemverilog
   :caption: test/base.sv

    class base#(
        int unsigned DATA_WIDTH
    ) extends uvm_test;
        `m_uvm_object_registry_internal(test::base#(DATA_WIDTH), test::base)
        `m_uvm_get_type_name_func(test::base)

        uvm_fifox::env #(DATA_WIDTH) m_env;

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            m_env = uvm_fifox::env #(DATA_WIDTH)::type_id::create("m_env", this);
        endfunction

         // ------------------------------------------------------------------------
        // run sequences on their sequencers
        virtual task run_phase(uvm_phase phase);
            time time_end;

            phase.raise_objection(this);
            begin
                reg_sequence reg_seq;

                reg_seq = reg_sequence::type_id::create("reg_seq");
                assert(reg_seq.randomize() with {enabled == 1;}) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize register sequence");
                reg_seq.m_regmodel = m_env.m_sequencer.m_regmodel;
                reg_seq.start(m_env.m_sequencer);
            end

            fork

                // Reset DUT
                begin
                    uvm_reset::sequence_start seq_rst;

                    seq_rst = uvm_reset::sequence_start::type_id::create("seq_rst", this);
                    assert(seq_rst.randomize()) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize reset sequence");
                    seq_rst.start(m_env.m_sequencer.m_reset);
                end
            join_none

            // RUN RX sequences
            fork // Here code would work the same as if fork had not been there.
                begin
                    uvm_logic_vector::sequence_simple #(DATA_WIDTH) seq_rx;

                    seq_rx = uvm_logic_vector::sequence_simple #(DATA_WIDTH)::type_id::create("seq_rx", this);
                    assert(seq_rx.randomize()) else `uvm_fatal(this.get_full_name(), "\n\tCannot randomize RX sequence");
                    seq_rx.start(m_env.m_sequencer.m_rx);
                end
            join

            // Wait for transactions inside DUT
            time_end = $time + 1000us;
            while ($time < time_end && m_env.used() == 1) begin
                #(500ns);
            end

            phase.drop_objection(this);

        endtask

        function void report_phase(uvm_phase phase);
            `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        endfunction
    endclass


----

===========
UVM Factory
===========

`The factory method <https://sourcemaking.com/design_patterns/factory_method>`_ is the design pattern which is used in
UVM to create UVM objects and UVM components. You can change the behaviour of sequences, objects and components by
using Factory. This ensures the variability of the verification environment. Don't forget to uncomment *typedef* in
*testbench.sv* with the correct test name

The function is used for overriding classes and changing their behaviour.
``void set_inst_override(uvm_object_wrapper override_type, string inst_path, uvm_component parent=null)``

This function registers the type which is created instead of the original type. This means that instead of object_1,
object_2 is going to be created in specific places.

.. code-block:: systemverilog
   :caption: test/base_extended.sv

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    class base_extended#(
        int unsigned DATA_WIDTH
    ) extends base#(DATA_WIDTH);
        `m_uvm_object_registry_internal(test::base_extended#(DATA_WIDTH), test::base_extended)
        `m_uvm_get_type_name_func(test::base_extended)

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            // Use factory to set low-level sequence to speed sequence.
            uvm_logic_vector_mvb::sequence_lib_rx #(1, DATA_WIDTH)::type_id::set_inst_override( // Original type
                uvm_logic_vector_mvb::sequence_lib_rx_speed #(1, DATA_WIDTH)::get_type(),       // New type
                "m_rx.*",                                                                       // Path to component
                this.env                                                                        // Start of path to component
            );
            super.build_phase(phase);
        endfunction

        function void report_phase(uvm_phase phase);
            `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        endfunction
    endclass


UVCs have a sequence which converts higher-level transactions to lower-level transactions. To create special
test scenarios, it is required to change these sequences and a sequence library. Or you want to create your own special sequence.
This is done by UVM factory methods.

A lot of UVCs have prepared the speed sequence. So it is possible to use it.

.. code-block:: systemverilog
   :caption: test/speed.sv

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    class speed#(
        int unsigned DATA_WIDTH
    ) extends base#(DATA_WIDTH);
        `m_uvm_object_registry_internal(test::speed#(DATA_WIDTH), test::speed)
        `m_uvm_get_type_name_func(test::speed)

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            // Use factory to set low-level sequence to speed sequence.
            uvm_logic_vector_mvb::sequence_lib_rx #(1, DATA_WIDTH)::type_id::set_inst_override( // Original type
                uvm_logic_vector_mvb::sequence_lib_rx_speed #(1, DATA_WIDTH)::get_type(),       // New type
                "m_rx.*",                                                                       // Path to component
                this.env                                                                        // Start of path to component
            );
            super.build_phase(phase);
        endfunction

        function void report_phase(uvm_phase phase);
            `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        endfunction
    endclass


You can create your own sequences and the sequence library. This represents
the maximal level of customisation, but it requires more time to develop.

.. code-block:: systemverilog
   :caption: test/my.sv

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    //Send valid frame only every fourth clock cycle
    class sequence_my #(
        int unsigned ITEM_WIDTH
    ) extends uvm_logic_vector_mvb::sequence_simple_rx_base #(1, ITEM_WIDTH);
        `uvm_object_param_utils(test::sequence_my #(ITEM_WIDTH))

        protected int unsigned delay;

        function new(string name = "sequence_full_speed_rx");
            super.new(name);
        endfunction

        //Send only every fourth clock cycle
        virtual task create_sequence_item();
            delay += 1;
            if (delay < 4) begin
                gen.src_rdy = 0;
            end else begin
                assert(ITEMS == 1) else `uvm_fatal(this.get_full_name(), "\n\tITEMS must be 1");
                hi_sqr.try_next_item(frame);
                if (frame != null) begin
                    `uvm_warning(m_sequencer.get_full_name(), "\n\tHigh level item is not prepared!");
                    gen.src_rdy = 0;
                end else begin
                    gen.vld[0] = 1'b1;
                    gen.data[0] = frame.data;
                    gen.src_rdy = 1'b1;

                    hi_sqr.item_done();
                    hl_transactions--;
                end
            end
        endtask

        task body();
            delay = 0;
            super.body();
        endtask
    endclass

    class sequence_lib_rx_my #(
        int unsigned ITEM_WIDTH
    ) extends uvm_logic_vector_mvb::sequence_lib_rx#(1, ITEM_WIDTH);
        `uvm_object_param_utils(test::sequence_lib_rx_my#(ITEM_WIDTH))
        `uvm_sequence_library_utils(test::sequence_lib_rx_my#(ITEM_WIDTH))

        function new(string name = "");
            super.new(name);
            init_sequence_library();
        endfunction

        virtual function void init_sequence(config_sequence param_cfg = null);
            if (param_cfg == null) begin
                this.cfg = new();
            end else begin
                this.cfg = param_cfg;
            end
            this.add_sequence(sequence_my#(ITEM_WIDTH)::get_type());
        endfunction
      endclass


    class my_test#(
        int unsigned DATA_WIDTH
    ) extends base#(DATA_WIDTH);
        `m_uvm_object_registry_internal(test::my_test#(DATA_WIDTH), test::my_test)
        `m_uvm_get_type_name_func(test::my_test)

        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            // Use factory to set low-level sequence to speed sequence.
            uvm_logic_vector_mvb::sequence_lib_rx #(1, DATA_WIDTH)::type_id::set_inst_override( // Original type
                sequence_lib_rx_my#(DATA_WIDTH)::get_type(),                                    // New type
                "m_env.m_rx.*",                                                                 // Path to component
                this                                                                             // Start of path to component
            );
            super.build_phase(phase);
        endfunction

        function void report_phase(uvm_phase phase);
            `uvm_info(this.get_full_name(), {"\n\tTEST : ", this.get_type_name(), " END\n"}, UVM_NONE);
        endfunction
    endclass


If you want to use these tests, you have to add test files into the pkg file. Register class in
testbench module ``typedef test::base_changed#(uvm_generic::DATA_WIDTH) speed;`` and ``typedef test::my_test#(uvm_generic::DATA_WIDTH) my_test;``.
To run test base_changed change line  ``set SIM_FLAGS(UVM_TEST) "test::base"``
to ``set SIM_FLAGS(UVM_TEST) "test::base_changed"`` or ``set SIM_FLAGS(UVM_TEST) "test::my_test"``

.. code-block:: systemverilog
   :caption: testbench.sv

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import uvm_generic::*;

    module testbench;
        // Create test with parameters (Register in factory)
        typedef test::base#(uvm_generic::DATA_WIDTH) base;
        typedef test::base_extended#(uvm_generic::DATA_WIDTH) base_extended;
        typedef test::base_extended#(uvm_generic::DATA_WIDTH) speed;
        typedef test::base_extended#(uvm_generic::DATA_WIDTH) my_test;

        // Create clock
        logic CLK = 0;
        always #(CLK_PERIOD/2) CLK = ~CLK;

        reset_if reset (CLK);
        mvb_if #(1, DATA_WIDTH)     mvb_rx    (CLK);
        mvb_if #(1, DATA_WIDTH)     mvb_tx    (CLK);

        mi_if  #(32, 32)            config    (CLK);


       initial begin
            uvm_root m_root;

            // REGISTER INTERFACE INTO DATABASE
            uvm_config_db #(virtual reset_if)::set(null, "", "vif_reset", reset);
            uvm_config_db #(virtual mvb_if #(1, DATA_WIDTH))    ::set(null, "", "vif_mvb_rx",     mvb_rx    );
            uvm_config_db #(virtual mvb_if #(1, DATA_WIDTH))    ::set(null, "", "vif_mvb_tx",     mvb_tx    );
            uvm_config_db #(virtual mi_if  #(32, 32))           ::set(null, "", "vif_mi",         config    );

            // STOP on end of simulation and dont print message ILLEGALNAME
            m_root = uvm_root::get();
            m_root.finish_on_completion = 0;
            m_root.set_report_id_action_hier("ILLEGALNAME", UVM_NO_ACTION);

            // DONT RECORD TRANSACTIONS
            uvm_config_db #(int)            ::set(null, "", "recording_detail", 0);
            uvm_config_db #(uvm_bitstream_t)::set(null, "", "recording_detail", 0);

            // RUN TESTS
            run_test();
            // STOP ON END OF SIMULATION
            $stop(2);
        end

        //INSTANTIATE DUT
        logic full;
        logic empty;
        FIFOX #(
            .DATA_WIDTH          (uvm_generic::DATA_WIDTH         ),
            .ITEMS               (uvm_generic::ITEMS              ),
            .RAM_TYPE            (uvm_generic::RAM_TYPE           ),
            .DEVICE              (uvm_generic::DEVICE             ),
            .ALMOST_FULL_OFFSET  (uvm_generic::ALMOST_FULL_OFFSET ),
            .ALMOST_EMPTY_OFFSET (uvm_generic::ALMOST_EMPTY_OFFSET),
            .FAKE_FIFO           (uvm_generic::FAKE_FIFO          )
        ) VHDL_DUT_U (

            .CLK   (CLK),
            .RESET (RST),

            .DI     (mvb_rx.DATA),
            .WR     (mvb_rx.SRC_RDY & mvb_rx.VLD[0]),
            .FULL   (full),
            .AFULL  (),
            .STATUS (),

            .DO     (mvb_tx.DATA   ),
            .RD     (mvb_tx.DST_RDY),
            .EMPTY  (empty         ),
            .AEMPTY ()

        );


        // CREATE REGISTER
        logic enable = '0;
        always @(posedge CLK)
        begin
            if(config.WR == 1'b0 and config.ADDR == '0) begin
                enable <= config.DWR[0];
            end
        end

        assign config.ARDY    = config.WR | config.RD;
        assign config.DRDY    = config.RD;
        assign config.DRD[0]  = enable;

        assign mvb_rx.DST_RDY = ~full;
        assign mvb_tx.SRC_RDY = ~empty & enable;
        assign mvb_tx.VLD     = '1;
    endmodule


.. code-block:: systemverilog
   :caption: test/pkg.sv

    `define FIFOX_TEST_SV
    package test;
        `include "uvm_macros.svh"
        import uvm_pkg::*;

        `include "base.sv"
        `include "base_changed.sv"
        `include "my_test.sv"
        `include "speed.sv"
    endpackage
    `endif


----

======================
Sequence Configuration
======================

There is a simpler possibility of sequence configuration. Some sequences
have a configuration object. A configuration object can be assigned by a function
``virtual function void config_set(CONFIG_TYPE cfg)``

.. code-block:: systemverilog
   :caption: comp/uvm/logic_vector_array_mfb/config.sv

    class config_sequence extends uvm_object;
        `uvm_object_utils(uvm_logic_vector_array_mfb::config_sequence)

        uvm_common::sequence_cfg state;

        //configure space between packet
        int unsigned space_size_min     = 0;
        int unsigned space_size_max     = 200;
        // configuration of probability of rdy signal in percentage
        int unsigned rdy_probability_min = 0;   // inside [0:100:ta]
        int unsigned rdy_probability_max = 100; // inside [0:100]
        // Straddling is used only with seq_type == "PCIE"
        logic straddling                 = 0;

        typedef enum {INVALID_ZERO, INVALID_UNDEF, INVALID_RAND} invalid_val_t;
        invalid_val_t generate_invalid;

        function new(string name = "uvm_logic_vector_array_mfb::config_sequence");
            super.new(name);
            state = null;
            generate_invalid = INVALID_RAND;
        endfunction

        function void probability_set(int unsigned min, int unsigned max);
            rdy_probability_min = min;
            rdy_probability_max = max;
        endfunction

        function void straddling_set(logic value);
            straddling = value;
        endfunction

        function void space_size_set(int unsigned min, int unsigned max);
            space_size_min = min;
            space_size_max = max;
        endfunction
    endclass


Setup the configuration object to lower level sequences

.. code-block:: systemverilog
   :caption: env/env.sv

    class env #(
        int unsigned DATA_WIDTH
    ) extends uvm_env;
        `uvm_component_param_utils(uvm_fifox::env #(DATA_WIDTH));

        // Virtual sequencer
        sequencer #(DATA_WIDTH) m_sequencer;

        // RESET interface
        protected uvm_reset::agent m_reset;
        // RX environments
        protected uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH) m_rx;
        // TX environments
        protected uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH) m_tx;

        // Scoreboard
        protected scoreboard #(DATA_WIDTH) sc;

        // Constructor
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
        endfunction

        // Create base components of environment.
        function void build_phase(uvm_phase phase);
            uvm_reset::config_item m_cfg_reset;
            uvm_logic_vector_mvb::config_item m_cfg_rx;
            uvm_logic_vector_mvb::config_item m_cfg_tx;

            //Call parents function build_phase
            super.build_phase(phase);

            //Create reset environment
            m_cfg_reset                = new;
            m_cfg_reset.active         = UVM_ACTIVE;   // Activly driven environment
            // interface register name have to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_reset.interface_name = "vif_reset";
            uvm_config_db #(uvm_reset::config_item)::set(this, "m_reset", "m_config", m_cfg_reset);
            // Creation of the reset
            m_reset = uvm_reset::agent::type_id::create("m_reset", this)


            // Configuration of the m_env_mvb_rx
            m_cfg_rx                = new;
            m_cfg_rx.active         = UVM_ACTIVE;
            // interface register name have to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_rx.interface_name = "vif_mvb_rx";
            // configure sequence
            // m_cfg_rx.seq_cfg = m_cfg.seq_rx_cfg;
            m_cfg_rx.seq_cfg = new();
            m_cfg_rx.space_size_set(2, 5);
            m_cfg_rx.probability_set(70, 100);
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_rx", "m_config", m_cfg_rx);
            // Creation of the m_env_mvb_rx
            m_env_mvb_rx = uvm_logic_vector_mvb::env_rx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_rx", this);

            // Configuration of the m_env_mvb_tx
            m_cfg_tx                = new;
            m_cfg_tx.active         = UVM_ACTIVE;
            // interface register name have to be same in the testbench uvm_config_db#(...)::set();
            m_cfg_tx.interface_name = "vif_mvb_tx";
            uvm_config_db #(uvm_logic_vector_mvb::config_item)::set(this, "m_env_mvb_tx", "m_config", m_cfg_tx);
            // Creation of the m_env_mvb_tx
            m_env_mvb_tx = uvm_logic_vector_mvb::env_tx #(1, DATA_WIDTH)::type_id::create("m_env_mvb_tx", this);
        endfunction

        // Connect agent's ports with ports from scoreboard.
        function void connect_phase(uvm_phase phase);
            // Connection of the reset
            m_reset.sync_connect(m_rx.reset_sync);
            m_reset.sync_connect(m_tx.reset_sync);

            // Connection to scoreboard
            m_rx.analysis_port.connect(sc.analysis_imp_mvb_rx);
            m_tx.analysis_port.connect(sc.analysis_imp_mvb_tx);

            // Connect sequencer
            m_sequencer.m_reset = m_reset.m_sequencer;
            m_sequencer.m_rx    = m_rx.m_sequencer;
        endfunction
    endclass



----

====
PCAP
====


You can read and write data to pcap files. Below is a simple code converting
captured packet to logic_vector_array::sequence_item. Here is some
`example <https://gitlab.liberouter.org/ndk/ndk-fpga/-/blob/devel/comp/uvm/packet_generators/sequence_search.sv?ref_type=heads>`_

.. code-block:: systemverilog
   :caption: sequence.sv

    class sequence_pcap #(int unsigned ITEM_WIDTH) extends uvm_sequence#(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH));
        `uvm_object_param_utils(test::sequence_pcap #(ITEM_WIDTH))

        string pcap_name = "test.pcap"
        // Instatiate pcap readere
        protected uvm_pcap::reader reader;

        function new(string name);
            super.new(name);
            reader = new();
        endfunction

        task body();
            byte unsigned data[];

            // Open pcap file
            reader.open(pcap_name);

            req = uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)::type_id::create("req", m_sequencer);
            //Read data from pcap
            while(reader.read(data) == uvm_pcap::RET_OK) begin
                start_item(req);
                // convert data to transaction
                req.data = { >>{ data } };
                finish_item(req);
            end

            // close pcap file
            reader.close();
        endtask
    endclass


----

==========================================
Register configuration by external program
==========================================

In the NDK-FPGA environment an external program can comunacte with the DUT.
If you want to use an external program, you have to create the register model with uvm_mem.
(Others component, such as uvm_reg, is not tested).

.. code-block:: systemverilog
   :caption: regmodel.sv

    // regmodel.sv: Register model of KDST
    // Copyright (C) 2023 CESNET z. s. p. o.
    // Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>

    class kdst_regmodel extends uvm_reg_block;
        `uvm_object_param_utils(uvm_key_data_storage::kdst_regmodel)

        uvm_mem kdst;
        localparam MEM_BYTE_WIDTH = 4;

        function new(string name = "reg_block");
            super.new(name);
        endfunction

        function void set_frontdoor(uvm_reg_frontdoor frontdoor);
            uvm_reg_frontdoor c_frontdoor;

            $cast(c_frontdoor, frontdoor.clone());
            kdst.set_frontdoor(c_frontdoor);
        endfunction

        virtual function void build(uvm_reg_addr_t base, int unsigned bus_width);
            kdst = new("kdst", 'h300/MEM_BYTE_WIDTH, 8*MEM_BYTE_WIDTH);
            kdst.configure(this);

            //create map
            this.default_map = create_map("MAP", base, bus_width/8, UVM_LITTLE_ENDIAN);
            this.default_map.add_mem(kdst, 0, .rights("RW"));
            //Add registers to map

            this.lock_model();
        endfunction
    endclass


External program can write to *uvm_mem* and reads from *uvm_mem*. Extends class nfb_driver::mi_sequence. This class
use GRPC server and client to maintain interprocess communication. Execute program in task ``run_program``.
The program will be automatically executed after you call the task ``my_seq.start``.


.. code-block:: systemverilog
   :caption: reg_sequence.sv

    virtual class run_external_program extends nfb_driver::mi_sequence;
        `uvm_object_param_utils(uvm_key_data_storage::mi_sequence_base)

        protected uvm_key_data_storage::kdst_regmodel m_regmodel;
        protected string prog_path = "`/../../../sw/build/src/cttctl/cttctl";

        function new(string name = "mi_sequence_base");
            super.new(name);
        endfunction

        task body;
            if(!uvm_config_db#(uvm_key_data_storage::kdst_regmodel)::get(null, "", "m_regmodel", m_regmodel)) begin
                `uvm_fatal(this.get_full_name(), "Could not find regmodel")
            end

            this.component_set(m_regmodel.kdst);
            super.body();
        endtask

        task run_program();
            uvm_common::prog prog;
            string cmd;
            string param = "";
            bit [KEY_WIDTH - 1 : 0] key;

            prog = uvm_common::prog::type_id::create("prog", null);
            param = "-a --param2";
            cmd  = {"`dirname ", `__FILE__, prog_path,
                    param,  " >>prog_out 2>>prog_err"};

            prog.call(cmd);
        endtask
    endclass




