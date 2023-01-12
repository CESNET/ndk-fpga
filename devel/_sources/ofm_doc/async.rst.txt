Asynchronous modules
====================

**ASYNC_BUS_HANDSHAKE** - General asynchronous/clock domain crossing for multi-bit signals and buses. It uses a handshake mechanism and has significantly lower throughput (one transfer per ~10 clock cycles) than the dual clock FIFOs.

**ASYNC_GENERAL** - General asynchronous/clock domain crossing for single-bit signals only. Detection mode can be configured (rising edge, falling edge).

**ASYNC_OPEN_LOOP** - Simpler asynchronous/clock domain crossing for single-bit signals, which require specific clock frequency ratio.

**ASYNC_OPEN_LOOP_SMD** - Same as OPEN_LOOP but with ``set_max_delay`` constraint. This variant is useful for clock domain crossing individual bits of counters in Gray coding.

**ASYNC_RESET** - Synchronization of reset signal into specific clock domain. The output reset is activated asynchronously (immediately) and deactivated synchronously with the rising edge of the target clock signal.

.. warning::
   Only the ASYNC_BUS_HANDSHAKE or one of the dual clock FIFOs can be used to transmit a general multi-bit signal! The list of dual clock FIFOs can be :ref:`found here<asfifo_modules>`.

.. toctree::
   :maxdepth: 1
   :caption: Detailed documentation:
          
.. comp/base/async/open_loop/index           
.. Add more references here...

References
^^^^^^^^^^

For more detailed description refer to `Jakub Cabal's bachelor thesis <https://www.vutbr.cz/studenti/zav-prace/detail/85920>`_ (2014/2015).
