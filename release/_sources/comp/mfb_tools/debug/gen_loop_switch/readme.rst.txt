.. _gls_debug:

Gen Loop Switch (GLS)
---------------------

.. vhdl:autoentity:: GEN_LOOP_SWITCH

Control software
^^^^^^^^^^^^^^^^

The Gen Loop Switch (GLS) module can be controlled using the `GenLoopSwitch` class located in the `ofm` Python package at `ofm.comp.mfb_tools.debug.gen_loop_switch.gen_loop_switch`.
There is also the `ofm-gls` command-line tool available after the package installation.

A script that uses the `GenLoopSwitch` class is provided here in the `./sw` directory.
This script is performs throughput measurements in various modes and is the base for many HW tests.
See the :ref:`GLS module tutorial <ndk_testing_gls>` for more information.
