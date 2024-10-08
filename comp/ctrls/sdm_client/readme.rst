.. _sdm_client:

SDM CLIENT
----------

This component acts as a bridge between a host and the SDM (Secure Device Manager) on Intel FPGAs (Stratix 10, Agilex).
It converts MI to Avalon-MM interface and uses Mailbox Client FPGA IP to send commands and obtain status information from the SDM peripheral clients.
There are multiple pre-defined functions available:

* Reading the Chip ID
* Reading temperature sensors
* Reading voltage sensors
* Reading and writing external QSPI (Quad Serial Peripheral Interface) flash memory
* Performing RSU (Remote System Update)

Specification
^^^^^^^^^^^^^

Avalon-MM and Mailbox Client IP use 32bit word addressing.
In order to avoid working with unaligned addresses, MI addresses are shifted 2 bits to the right (word align) and after that 4 lowest bits are used for Mailbox Client's OFFSET (spans from 0 to 10).
Mailbox Client IP uses a command fifo on OFFSET[0] where you should direct the commands and their arguments in a sequence.

.. warning::
    Mailbox Client FPGA IP does not support *waitrequest* signal, thus the signal is set to ground (always able to accept requests) and capacity of its command fifo must be checked by reading client's memory on OFFSET[2] in software.

MI bus does not support interrupt (*irq*) signal, so it is left open.
Interrupt enable (IER) and status registers (ISR) are accessible by reading client's memory on OFFSET[7] and OFFSET[8] respectively.

See `Mailbox Client Intel FPGA IP User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/ug/ug-20087.pdf>`_ for more detailed information.

Block diagram
^^^^^^^^^^^^^

.. image:: doc/sdm_client_arch.svg
   :align: center
   :width: 50 %

More references
^^^^^^^^^^^^^^^

* See `Intel Stratix 10 Configuration User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/stratix-10/ug-s10-config.pdf>`_ or `Intel Agilex Configuration User Guide <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/hb/agilex/ug-ag-config.pdf>`_ (section 1.2.1.) for more information on SDM and (section 5) on RSU.

* See :ref:`MI2AVMM<mi2avmm>` for more information about the interface converter.
