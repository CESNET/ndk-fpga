.. _mem_logger:

Memory Logger
-------------

The **Mem Logger** is a wrapper around the :ref:`DATA_LOGGER <data_logger>` component.
It logs simple statistics about a memory interface.

Usage example can be found in the :ref:`MEM_TESTER <mem_tester>` component.

Key Features
^^^^^^^^^^^^

Measured Statistics
"""""""""""""""""""

* Number of read and write requests
* Number of transferred words
  (separately tracks requested read words vs. actually received read words)
* Number of clock cycles between first and last transaction for:

    * Read operations
    * Write operations
    * Combined read + write traffic

  (software can calculate effective data throughput from these)
* Read request latencies:

    * Minimum, maximum and average latency
    * Latency histogram

  Internally uses the :ref:`LATENCY_METER <latency_meter>` and :ref:`HISTOGRAMER <histogramer>` components.

Configuration
"""""""""""""

* Option to measure read latency to the **first** or **last** received word
  (default: last word)

Component port and generics description
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: MEM_LOGGER
   :noautogenerics:


Instance template (simple usage)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block::

    mem_logger_i : entity work.MEM_LOGGER
    generic map (
        MEM_DATA_WIDTH          => MEM_DATA_WIDTH       ,
        MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH       ,
        MEM_BURST_COUNT_WIDTH   => MEM_BURST_WIDTH      ,
        MEM_FREQ_KHZ            => AMM_FREQ_KHZ         ,

        MI_DATA_WIDTH           => MI_DATA_WIDTH        ,
        MI_ADDR_WIDTH           => MI_ADDR_WIDTH
    )
    port map (
        CLK                     => MEM_CLK                  (i),
        RST                     => MEM_RST                  (i),

        MEM_READY               => MEM_AVMM_READY           (i),
        MEM_READ                => MEM_AVMM_READ            (i),
        MEM_WRITE               => MEM_AVMM_WRITE           (i),
        MEM_ADDRESS             => MEM_AVMM_ADDRESS         (i),
        MEM_READ_DATA           => MEM_AVMM_READDATA        (i),
        MEM_WRITE_DATA          => MEM_AVMM_WRITEDATA       (i),
        MEM_BURST_COUNT         => MEM_AVMM_BURSTCOUNT      (i),
        MEM_READ_DATA_VALID     => MEM_AVMM_READDATAVALID   (i),

        MI_DWR                  => mem_mi_dwr               (i),
        MI_ADDR                 => mem_mi_addr              (i),
        MI_BE                   => mem_mi_be                (i),
        MI_RD                   => mem_mi_rd                (i),
        MI_WR                   => mem_mi_wr                (i),
        MI_ARDY                 => mem_mi_ardy              (i),
        MI_DRD                  => mem_mi_drd               (i),
        MI_DRDY                 => mem_mi_drdy              (i)
    );


Control Software
^^^^^^^^^^^^^^^^

For installation instructions, see the :ref:`DATA_LOGGER <data_logger>` documentation.

You can use the ``mem_logger`` Python module from your own scripts, or run the tool directly:

.. code-block:: console

    python3 mem_logger.py
