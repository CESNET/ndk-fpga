.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. AXI agent and AXI interface
.. _uvm_axi:

*********
AXI Agent
*********

This agent is responsible for communication through the AXI interface. This is a low-level agent which generates only simple AXI words. For advanced control use the logic_vector_array_axi.

The environment is configured by three parameters:

- DATA_WIDTH
- TUSER_WIDTH
- REGIONS

sequence_item
---------------------------

This package contains two agents. The RX agent sends data to the DUT and the TX agent samples the received data. Sequence run in the RX agent generates TDATA, TUSER, TKEEP, TLAST, and TVALID
variables in a sequence_item. One clock cycle later, the driver sets the TREADY variable in the sequence_item as a response. The TX agent receives data from the DUT. It
is required to generate TREADY and drive TDATA, TUSER, TKEEP, TLAST, and TVALID as a response one clock cycle later.

The following table shows variables in the sequence_item class.

.. code-block:: systemverilog

    logic [DATA_WIDTH  -1 : 0] tdata;
    logic [TUSER_WIDTH -1 : 0] tuser;
    logic [TKEEP_WIDTH -1 : 0] tkeep;
    logic                      tlast;
    logic                      tvalid;
    logic                      tready;

This is low level protocol if you generate data in sequence please be carefull if you dont breaking axi protocols rules.
