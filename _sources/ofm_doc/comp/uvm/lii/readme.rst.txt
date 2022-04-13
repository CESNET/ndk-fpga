.. readme.rst: Documentation of single component
.. Copyright (C) 2021 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
.. Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
.. Author(s): Dan Kříž <xkrizd01@vutbr.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. LII interface
.. _uvm_mii:


************
LII agent
************
Agent is used for connecting of all components (driver, monitor,...). Agent has his own configuration object which contains two parameters: active (when is up then agent is active in other way is passive) and interface which say name of the interface that is used.
When agent is active then sequencer and driver are created amd connected to interface. When is passive then only monitor is created.

LII interface
-------------
LII (Media-independent interface) bus is interface which allows communication throught 10g low latency ethernet. There are asserts which check if EEOF is asserted right and if SOF and EOF are coming in right ordder. Link for detailed description of LII bus is here: `<https://gitlab.liberouter.org/ndk/hft/-/tree/friedl-feat-ethphy/comp/eth_phy/10ge/top>`_

LII bus description
^^^^^^^^^^^^^^^^^^^
LII bus has these 5 ports + 2 ports optional (EEOF and EDB) which depends on parameter FAST_SOF. In verification interface are asserts which check these events.

Generics
^^^^^^^^
===================  =============  ============  =====================================================
Name                 Type           Default       Description
===================  =============  ============  =====================================================
DATA_WIDTH           natural        32            Data word width in bits.
FAST_SOF             natural        0             Fast SOF mode enable. Saves one cycle latency, but the logic is more complex
===================  =============  ============  =====================================================

Ports
^^^^^
=============  ===  ==================     ======================================================
Name           Dir  Dimension              Description
=============  ===  ==================     ======================================================
DATA           IN   DATA_WIDTH             TX data. On the first data within an frame, only bit 31:8 are 
BYTES_VLD      IN   DATA_WIDTH             valid bytes in the the last word in range 0x1 to 0x4. Valid on EOF cycle 
SOF            IN   1                      Start of data frame, single clock cycle 
EOF            IN   1                      End of data frame, single clock cycle 
RDY            IN   1                      TX data. On the first data within an frame, only bit 31:8 are 
EEOF           IN   1                      Early end of data frame, single clock cycle pulse
EDB            IN   DATA_WIDTH             Early valid bytes
=============  ===  ==================     ======================================================

LII sequence item
-----------------
Sequence item contains basic ports from interface, except EEOF and EDB which are only drived to interface by driver. All signals which are in sequence item are randomized.
There are three methods:

- ``do_copy`` is used for copying of the transaction. 
- ``do_compare`` is used for comparing data of two transactions.
- ``convert2string`` is used for printing whole transaction.

LII monitor
-----------
LII monitor is used for monitoring of traffic. There is only easy monitor which write whole transaction to analysis port when reset is not asserted.

LII driver
----------
LII driver is used for driving LII transactions to interface. There is used one parameter ``FAST SOF``, when this parameter is asserted then driver driving ``EEOF`` and ``EDB`` to interface. ``EEOF`` and ``EDB`` is drived only when in the next transaction is asserted ``EOF``, ``EDB`` must be same as ``BYTES_VLD`` in next transaction.
