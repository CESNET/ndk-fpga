.. _ndk_mem:
.. _ndk_intel_mem:

The Memory Controller
=====================

Many FPGA cards include external memory (very often DDR4) and the NDK is ready to support them. Depending on the FPGA type and the specific FPGA card, an external memory controller is instantiated in the top-level of the NDK firmware. Currently, three memory controller IPs are supported in the NDK:

- `Intel Stratix 10 EMIF IP for DDR4 <https://www.intel.com/content/www/us/en/docs/programmable/683741/>`_
- `Intel Agilex EMIF IP for DDR4 <https://www.intel.com/content/www/us/en/docs/programmable/683216/>`_
- `UltraScale Architecture-Based FPGAs Memory IP for DDR4 <https://docs.xilinx.com/v/u/en-US/pg150-ultrascale-memory-ip>`_

Each supported controller uses a slightly different user interface (Intel EMIF uses Avalon-MM, Xilinx UltraScale Memory IP uses AXI4). The NDK uses only the Avalon-MM to keep the access from the user application to the external memory simple (see the `Avalon Interface Specifications <https://www.intel.com/content/www/us/en/docs/programmable/683091/>`_). In the case where the Xilinx UltraScale Memory IP is instantiated, the AXI4 to Avalon-MM bus converter is automatically instantiated as well.

.. note::

    The NDK-based reference application (ndk-app-minimal) contains a module :ref:`Mem Tester <mem_tester>` in the Application space for testing communication with external memory and measure their basic properties (throughput, latency).
