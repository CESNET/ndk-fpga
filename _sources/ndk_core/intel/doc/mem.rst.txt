.. _ndk_intel_mem:

Memory controller (EMIF)
^^^^^^^^^^^^^^^^^^^^^^^^

To access external memory (typically DDR4) on an Intel FPGA, our platform uses standard External Memory Interface (EMIF) Hard IP blocks.
These are suitably configured, and their Avalon-MM user interface is integrated into :ref:`the application core <ndk_app>`.
Please read the EMIF user guide and Avalon-MM bus specifications.

.. note::

    The prepared basic application core then contains :ref:`debug modules <mem_tester>` that can test communication with these memories and measure their basic properties (throughput, latency).

**References**

- `External Memory Interfaces Intel Stratix 10 FPGA IP User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-emi.pdf>`_
- `External Memory Interfaces Intel Agilex FPGA IP User Guide (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/agilex/ug-ag-emi.pdf>`_
- `Avalon Interface Specifications (external) <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/manual/mnl_avalon_spec.pdf>`_
