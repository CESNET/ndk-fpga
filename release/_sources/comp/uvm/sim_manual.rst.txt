.. readme.rst: Documentation of single component
.. Copyright (C) 2023 CESNET z. s. p. o.
.. Author(s): Dan Kříž    <danielkriz@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. UVM simulation
.. _uvm_simulation:

UVM simulation
###############

UVM simulation is a tool that can be used by FW developers to create baseline tests for their components.
This section will explain how to create a UVM simulation.

Examples
********

This section contains examples of the UVM simulation.
Every example is located in the uvm_sim folder.
All examples contain only the most necessary files (UVM components).
Out of the components described earlier, only the Environment, Virtual Sequencer, Virtual Sequence, DUT, Testbench, and Test are used.
Finally, for each UVM simulation, there is a ``sequence_tb.sv`` file, which is different for each component.
This file contains a sequence for every interface (MFB, MVB, MI).
The developer defines a set of transactions in each sequence he wants to generate.
The following three examples are for the most commonly used combinations of interfaces: MFB + MI, MVB + MI, and MFB + META/MVB.
The following subsections will describe what the sequences look like and how to modify them to use them for another component.

MFB + MI
========

The first example is a simulation of the `Speed Meter <https://gitlab.liberouter.org/ndk/ofm/-/tree/devel/comp/mfb_tools/logic/speed_meter>`_ component that uses MFB and MI interfaces.
There are two sequences in the ``sequence_tb.sv`` file, ``sequence_mi.sv`` for the MI interface and ``sequence_mfb_data.sv`` for the MFB interface.
The first one inherits from the ``sequence_mi_sim``, which is located in the uvm_mi pkg (for more information see, the :ref:`UVM MI documentation<uvm_mi>`).
There is a defined set of MI commands that controls the component.

.. code-block:: systemverilog

    virtual task create_sequence_item();
        uvm_mi::sequence_item_response #(DATA_WIDTH) rsp;
        rsp = uvm_mi::sequence_item_response #(DATA_WIDTH)::type_id::create("rsp");

        #(50*CLK_PERIOD)
        // Read ticks counter
        // Read request (Default value of BE = '1)
        //   ADDR
        read(10'h0);
        // Read max ticks counter
        read(10'h4);
        // Read bytes counter
        read(10'h8);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

        #(50*CLK_PERIOD)
        // Read ticks counter
        // Read request (Default value of BE = '1)
        //   ADDR
        read(10'h0);
        // Read max ticks counter
        read(10'h4);
        // Read bytes counter
        read(10'h8);
        // Clear counter
        // Write request (Default value of BE = '1)
        //    ADDR   DATA
        write(10'hc, 32'h1);

        // Print last three read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

    endtask

The second one creates a data array for the MFB interface.
It is possible to define the structure of the MFB packet (e.g., create a custom header).
For example, if you want to construct a packet with random values, where you want to define its size, you can use the ``uvm_do_with`` macro with only the size defined.

.. code-block:: systemverilog

    // Send random data with specific size
    `uvm_do_with(req, {data.size == 137;  });
    `uvm_do_with(req, {data.size == 62;   });
    `uvm_do_with(req, {data.size == 74;   });
    `uvm_do_with(req, {data.size == 256;  });
    `uvm_do_with(req, {data.size == 1024; });
    `uvm_do_with(req, {data.size == 500;  });

The second example shows how to create a packet that contains a header at its start.

.. code-block:: systemverilog

    // Send random data with specific header
    start_item(req);
    m_data = new[136];
    std::randomize(m_data);
    // Header contains only data size
    header   = m_data.size();
    req.data = new[m_data.size()+header_width/ITEM_WIDTH];
    req.data = {header, m_data};
    finish_item(req);

The third example shows how to create a packet with specific data.

.. code-block:: systemverilog

    // Send specific data with specific size
    start_item(req);
    req.data = {8'h04, 8'h4c, 8'h1f, 8'hfe, 8'hf0, 8'h50, 8'h7a, 8'h02};
    finish_item(req);

    // Send specific data with specific size different way
    start_item(req);
    req.data = new[16];
    // Divide data word to ITEM_WIDTH chunks and insert them to array
    { >>{req.data}} = 'hf404f404f404f404;
    finish_item(req);

MFB + META/MVB
==============

The second example is a simulation of the `Dropper <https://gitlab.liberouter.org/ndk/ofm/-/tree/devel/comp/mfb_tools/flow/dropper>`_ component that uses the MFB interface with metadata.
There are two sequences in the ``sequence_tb.sv`` file, ``sequence_mfb_data.sv`` for the MFB interface and ``sequence_meta.sv`` for metadata.
The first one is the same as in the previous example, and the second one generates random metadata and drop signal.
The number of metadata transactions have to be same as number of MFB transactions.
In other case, the simluation will stuck.

.. code-block:: systemverilog

    // Send random meta with asserted drop signal
    start_item(req);
    void'(std::randomize(m_meta));
    drop   = 1'b1;
    // In the DUT the drop and metadata will be in one signal
    req.data = {drop, m_meta};
    finish_item(req);

    // Send random meta with deasserted drop signal
    start_item(req);
    void'(std::randomize(m_meta));
    drop   = 1'b0;
    // In the DUT the drop and metadata will be in one signal
    req.data = {drop, m_meta};
    finish_item(req);

    // Send random meta with deasserted drop signal
    start_item(req);
    void'(std::randomize(m_meta));
    drop   = 1'b0;
    // In the DUT the drop and metadata will be in one signal
    req.data = {drop, m_meta};
    finish_item(req);

    // Send random meta with asserted drop signal
    start_item(req);
    void'(std::randomize(m_meta));
    drop   = 1'b1;
    // In the DUT the drop and metadata will be in one signal
    req.data = {drop, m_meta};
    finish_item(req);


MVB + MI
========

The last example is a simulation of the `Lookup Table <https://gitlab.liberouter.org/ndk/ofm/-/tree/devel/comp/mvb_tools/storage/lookup_table>`_ component that uses MVB interface with MI.
There are two sequences in the ``sequence_tb.sv`` file, ``sequence_mvb_data.sv`` for the MVB interface and ``sequence_mi.sv`` for the MI interface.
The first one generates data for MVB transactions.
For this purpose, the ``uvm_do_with`` macro is used, where the data are user-defined.

.. code-block:: systemverilog

    `uvm_do_with(req, {req.data == 10'd0;  });
    `uvm_do_with(req, {req.data == 10'd4;  });
    `uvm_do_with(req, {req.data == 10'd8;  });
    `uvm_do_with(req, {req.data == 10'd12; });
    `uvm_do_with(req, {req.data == 10'd16; });

The second sequence is the same as in the first example but contains different MI commands.

.. code-block:: systemverilog

    virtual task create_sequence_item();

        // Write request (Default value of BE = '1)
        //    ADDR     DATA
        write(10'd0,   32'hda7a5407);
        write(10'd512, 32'hda7a5411);
        write(10'd4,   32'heb7ab8cc);
        write(10'd516, 32'hda7a54cc);
        write(10'd8,   32'h6fbaaa52);
        write(10'd12,  32'h2474b6ac);
        write(10'd16,  32'hc4d1ce40);
        #(50*CLK_PERIOD)
        // Read request (Default value of BE = '1)
        //   ADDR
        read(10'd0);
        read(10'd4);
        read(10'd8);
        read(10'd12);
        read(10'd16);

        // Print last five read responses
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);
        get_rsp(rsp);
        `uvm_info(this.get_full_name(), rsp.convert2string() ,UVM_MEDIUM);

    endtask

How to use the UVM simulation
=============================

So that was a brief description with a few examples.
Now, if you want to use these examples for a component of your choice, here is a list of steps you have to do:

1. Copy an appropriate example (meaning with the right interfaces) to the folder with your simulation
2. Change instance of the component in the dut.sv file to the right one
3. Change parameters of the verification to your desires
4. In case your component has more interfaces similar to the ones in the examples, do:
    - Add appropriate verification interfaces to the dut.sv and testbench.sv files
    - Add their environments to the env.sv file
    - Add appropriate sequences to the sequence_tb.sv file
    - Add appropriate sequencers to the sequencer.sv file
    - Run these sequences in a virtual sequence in the same way as the others

