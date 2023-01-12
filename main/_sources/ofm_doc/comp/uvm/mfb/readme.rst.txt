.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž    <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. MFB agent and MFB interface
.. _uvm_mfb:

*********
MFB Agent
*********

This agent is responsible for the communication through the MFB interface. This is a low level agent which generates only simple MFB words. For advanced control use the byte_array_mfb.

The environment is configured by five parameters: For more information see :ref:`mfb documentation<mfb_bus>`.

============== =
Parameter
============== =
REGIONS
REGIONS_SIZE
BLOCK_SIZE
ITEM_WIDTH
META_WIDTH
============== =


sequence_item
---------------------------

This package containst two agents. RX agents send data to DUT. Sequence run in RX agent generate ITEMS, META, SOF_POS, EOF_POS, EOF, SOF, SRC_RDY
variables in sequence_item. Driver after clock cycle set DST_RDY variable in sequence_item as response. TX agent is reciving data from DUT. There
is required to generate DST_RDY and driver after clock cycle set ITEMS, META, SOF_POS, EOF_POS, EOF, SOF, SRC_RDY as response.

Following table shows variables in sequence_items class. The meaning of signals is the same as in :ref:`mfb documentation<mfb_bus>`.

===================================================================   =
Name                                                                  
===================================================================   =
logic [REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH] data[REGIONS]          
logic [META_WIDTH]                            meta[REGIONS]           
logic [$clog2(REGION_SIZE)]                   sof_pos[REGIONS]        
logic [$clog2(REGION_SIZE * BLOCK_SIZE)]      eof_pos[REGIONS]        
logic [REGIONS]                               sof                     
logic [REGIONS]                               eof                     
logic                                         src_rdy                 
logic                                         dst_rdy                 
===================================================================   =

This is low level protocol if you generate data in sequence please be carefull if you dont breaking mfb protocols rules.
