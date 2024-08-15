.. _mem_logger:

Mem logger
----------

Mem logger is wrap around :ref:`DATA_LOGGER<data_logger>` that is able to log common statistics about memory interface.
Example usage can be found in :ref:`MEM_TESTER<mem_tester>` component.

Key features
^^^^^^^^^^^^

* Measured statistics

    * Number of read and write requests and words (including requested read words and received read words)
    * Number of ticks between first and last read, write and both (SW can calculate data flow)
    * Read requests latencies (minimum, maximum, average and histogram)

        * :ref:`LATENCY_METER<latency_meter>` and :ref:`HISTOGRAMER<histogramer>` components are used

* You can specify if read latency should be measured to the first or last received word (default: to last word)


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



Control SW
^^^^^^^^^^

First install ``DATA_LOGGER`` package

* You also need to install ``python nfb`` package

.. code-block::

    cd data_logger/sw
    python3 setup.py install --user


Then you can call ``MEM_LOGGER`` module from your script or call ``MEM_LOGGER`` directly:

.. code-block::

    python3 mem_logger.py
