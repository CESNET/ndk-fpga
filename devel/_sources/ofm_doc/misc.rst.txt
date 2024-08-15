Miscellaneous
==============

**ADC_SENSORS** - Controller of the Temperature and Voltage ADC IPs for Intel Stratix 10 FPGA. It is controlled via the MI bus. ``CANDIDATE FOR MOVE to CTRLs folder!``

**CLK_GEN** - Old clock generator, is used in some simulation only. ``CANDIDATE FOR REMOVAL!``

**CROSSBARX** - This unit performs data transfer between two buffers connected on SRC_BUF and DST_BUF interfaces based on Transactions passed on the TRANS interface.
Detailed :ref:`documentation can be found here<crossbarx>`.

**DEFICIT_IDLE_COUNTER** - Calculates gap sizes for each input packet while maintaining deficit idle count according to Ethernet specification.

**EVENT_COUNTER** - The Event Counter is a debuging unit for receiving statistics of occurence frequency of a certain event.
It is made accessible through MI interface using the Event Counter MI Wrapper. Detailed :ref:`documentation can be found here<event_counter>`.

**FIFO_PIPE** - Generic pipe implemented using registers and FIFO memory in almost full mode. ``UNUSED, CANDIDATE FOR REMOVAL!``

**FIRST_ONE_DETECTOR** - Old behavioral implementation of first one detector in vector. ``CANDIDATE FOR REMOVAL! Use FIRST_ONE from base logic!``

**HYPER_PIPE** - Generic hyper pipe implemented using registers, optimized for Intel Stratix 10 FPGA. ``UNUSED, CANDIDATE FOR REMOVAL!``

**ID32** - Identification component, is a small component, which is used to detect design inside FPGA. Informations are stored inside registers which are accessible through dedicated 32 bit interface.

**INTERRUPT_MANAGER** - Interrupt agregator module, TODO description.

**PACKET_PLANNER** - The Packet Planner processes input packet headers by assigning addresses to an outside buffer space to each packet,
so that they are placed one after another with the needed inter-packet gaps and alignment. Detailed :ref:`documentation can be found here<packet_planner>`.

**PIPE** - Component for pipelining data paths with source and destination ready signals. Compatible with Xilinx and Intel FPGAs.

**PULSE_SHORT** - Component which is able to shorten arbitrary long pulses to one clock period of the output clock. Documentation can be found :ref:`here<pulse_short>`.

**RESET_TREE_GEN** - Simple wrapper of ASYNC_RESET for parallel reset synchronization. Compatible with Xilinx and Intel FPGAs.

**RR_ARBITER** - Generic arbitration controler uses round-robin algorithm. The arbitration result is ready in the same cycle as the request arrived.

**SLR_CROSSING** - Special pipe component to cross between super logic regions (slow wire) on some Xilinx FPGAs.

**TRANS_SORTER** - This unit converts out-of-order confirmations of transactions to the original order of the transactions.
Detailed :ref:`documentation can be found here<trans_sorter>`.

**WATCHDOG** - Data flow watchdog module, which checks whether the monitored bus is not stuck. TODO

.. toctree::
   :maxdepth: 1
   :hidden:

   comp/base/misc/crossbarx/readme
   comp/base/misc/trans_sorter/readme
   comp/base/misc/packet_planner/readme
   comp/base/misc/event_counter/readme
   comp/base/misc/pulse_short/readme
..   comp/base/misc/<something>
.. Add more references here...

