.. howto-others.rst: This document describe more complicated verification topic
.. Copyright (C) 2025 CESNET z. s. p. o.
.. Author(s): Radek Iša   <isa@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. UVM howto

----

.. _uvm_howto_others:

***************************
UVM HOWTO - Multiver script
***************************

This document covers automation and advanced topics: running many verification
runs with different parameters (multiver) and how automatic testing detects
success. It assumes you already have a working UVM verification (e.g. from the
:ref:`uvm_howto_first_ver`) and are familiar with the concepts in the
:ref:`uvm_howto_intro`.

In many cases, it is necessary to verify the design with many different generic
parameters to check if the design behaves correctly in all cases. For this
purpose, use the *multi_ver.py* script to verify the design with different
generic parameters.

Create file *uvm/ver_settings.py* in the component directory.
This file contains configuration for the multiver script, which executes multiple verifications
with different settings. Block *_combinations_* represents individual tests. In this example, there are four tests.
*Default* configuration is always used and rewritten with the later configuration.
*__core_params__* setup environment variables. Possible variable is
*UVM_TEST*, *CODE_COVERAGE*, *RAND_SEED* can also used other for configuration like *TILE*.

.. code-block:: python
   :caption: uvm/ver_settings.py

    SETTINGS = {
        # default combination. All parameters have to be in
        # package with generic. For example generic.sv
        "default" : {
            "DATA_WIDTH"          : "4",
            "ITEMS"               : "16",
            "RAM_TYPE"            : "AUTO",
            "DEVICE"              : "STRATIX10",
            "ALMOST_FULL_OFFSET"  : "2",
            "ALMOST_EMPTY_OFFSET" : "0",
            "FAKE_FIFO"           : "0",
            # Core params setup variable in environment
            "__core_params__"  : {"UVM_TEST" : "base" },
        },
        "test_speed" : {
            "__core_params__"  : {"UVM_TEST" : "speed" },
        },
        "more_items" : {
            "ITEMS"               : "128",
        },
        "less_items" : {
            "ITEMS"               : "2",
        },
        # test uses combination setup above
        "_combinations_" : {
            "test_base"        : ("default"),
            "test_name:speed"  : ("default", "test_speed"),
            "test_more_items"  : ("default", "more_items"),
            "test_sp_item"     : ("default", "less_items", "test_speed"),
        }
    }

To run the multiver script use the command ``python3 ../../../../build/scripts/multi_ver/multi_ver.py top_level.fdo generic.sv ver_settings.py``

+------------------------+-------------------------+-------------------------+
| parameter              | test_more_items         | test_sp_item            |
+========================+=========================+=========================+
| DATA_WIDTH             | 4                       | 4                       |
+------------------------+-------------------------+-------------------------+
| ITEMS                  | 128                     | 2                       |
+------------------------+-------------------------+-------------------------+
| RAM_TYPE               | AUTO                    | AUTO                    |
+------------------------+-------------------------+-------------------------+
| DEVICE                 | STRATIX10               | STRATIX10               |
+------------------------+-------------------------+-------------------------+
| ALMOST_FULL_OFFSET     | 2                       | 2                       |
+------------------------+-------------------------+-------------------------+
| ALMOST_EMPTY_OFFSET    | 0                       | 0                       |
+------------------------+-------------------------+-------------------------+
| FAKE_FIFO              | 0                       | 0                       |
+------------------------+-------------------------+-------------------------+
| __core_params__        | {"UVM_TEST" : "base"}   | {"UVM_TEST" : "speed"}  |
+------------------------+-------------------------+-------------------------+

----

********************************
UVM HOWTO - Generate environment
********************************

I create a simple `generator of UVM environment <https://github.com/radek-isa/uvm_gen>`_. The Generator use UVC from NDK-fpga project.
The generator uses an XML description of the verification environment. The generator doesn't generate a fully functional verification
environment. It is required to complete some function which cannot be generated that simply.
Like model behavioural, toplevel sequence behavioural and converting sequences.

First, we have to create an XML file describing the verification environment.

.. code-block:: xml
   :caption: fifo.xml

    <?xml version="1.0" encoding="utf-8"?>
    <testbench version="0.1">
        <!-- CREATE GENERIC  -->
        <generics>
            <DATA_WIDTH type="int unsigned"/>
            <ITEMS      type="int unsigned"/>
            <RAM_TYPE   type="string"/>
            <ALMOUST_FULL_OFFSET  type="int unsigned"/>
            <ALMOUST_EMPTY_OFFSET  type="int unsigned"/>
            <FAKE_FIFO   type="logic" value="1'b0"/>
            <DEVICE type="string"  value="STRATIX10"/>
        </generics>


        <!-- UVC connected to DUT interface  -->
        <agents>
            <reset name="rst">
            </reset>

            <logic_vector_mvb name="rx" reset="rst" dir="RX">
                <generics>
                    <ITEMS>1</ITEMS>
                    <ITEM_WIDTH>DATA_WIDTH</ITEM_WIDTH>
                </generics>

                <config>
                     <interface_name>"vif_rx"</interface_name>
                     <active>UVM_ACTIVE</active>
                </config>
            </logic_vector_mvb>

            <logic_vector_mvb name="tx" reset="rst" dir="TX">
                <generics>
                    <ITEMS>1</ITEMS>
                    <ITEM_WIDTH>DATA_WIDTH</ITEM_WIDTH>
                </generics>

                <config>
                     <interface_name>"vif_tx"</interface_name>
                     <active>UVM_ACTIVE</active>
                </config>
            </logic_vector_mvb>
        </agents>

        <!-- DUT connections  -->
        <dut name="DUT_U" entity="GEN_LOOP_SWITCH">
            <generics>
                <DATA_WIDTH>DATA_WIDTH</DATA_WIDTH>
                <ITEMS>ITEMS</ITEMS>
                <RAM_TYPE>RAM_TYPE</RAM_TYPE>
                <DEVICE>DEVICE</DEVICE>
                <ALMOUST_FULL_OFFSET> ALMOUST_FULL_OFFSET </ALMOUST_FULL_OFFSET>
                <ALMOUST_EMPTY_OFFSET>ALMOUST_EMPTY_OFFSET</ALMOUST_EMPTY_OFFSET>
                <FAKE_FIFO>FAKE_FIFO</FAKE_FIFO>
            </generics>

            <ports>
                <CLK   port="CLK"/>
                <RESET port="rst.RESET"/>

                <DI    port="rx.DATA"/>
                <WR    port="rx.SRC_RDY & rx.VLD[0]"/>
                <FULL  port="full"/>
                <AFULL port=""/>

                <STATUS port=""/>

                <DO     port="tx.DATA"/>
                <RD     port="~tx.DST_RDY"/>
                <EMPTY  port="empty"/>
                <AEMPTY port=""/>
            </ports>
        </dut>
    </testbench>


Now run command ``./main.py --file fifo.xml --out=uvm``. This command generates a template of the UVM environment.
Look at the generated code. To finish verification, it is required to write some code to the SV files.

----

******************************
UVM HOWTO - Generated Coverage
******************************


Generating the UCDB file in the QuestaSim
``coverage save -codeAll -cvg -assert  coverage.ucdb;``

This saves coverage from simulation.
Next command run in BASH. This command generates from the UCDB database html report
``vcover report -codeAll -cvg -assert -precision 4 -html -output cov_html -details -threshL 70 -threshH 95 final.ucdb``

Coverage from more verifications of the same component can be merged by the command.
``vcover merge merged.ucdb run_1.ucdb run_2.ucdb``


