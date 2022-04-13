.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. Common package contain common randomization object

.. _uvm_common:


COMMON PACKAGE
---------------------------

common package contain commonly used small components.


Random
^^^^^^^^^
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
        common::rand_rdy    rdy;    //inter frame gabs
        common::rand_length space;  //space between frames
        function new(string name, uvm_component parent = null);
            super.new(name, parent);
            rdy   = common::rand_rdy_rand::new();
            space = common::rand_length_rand::new();
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

