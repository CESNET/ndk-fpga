.. _data_logger:

Data logger
-----------

Data logger is used to log statistics about a specific events and make them available on the MI bus.
Simple usage can be seen in :ref:`MEM_LOGGER<mem_logger>` component.

Key features
^^^^^^^^^^^^

* Counter interface

    * Each counter interface contains a counter that can count
      the number of occurrences of a specific event, the number of clock cycles of a event, ...
    * The number of used counter interfaces is set via generic parameters
    * Width is common for every counter and can be set to any value (even larger than MI bus width)
    * If the counter should overflow, it will stay at the maximum possible value
    * Custom increment value can be used (default: 1)
    * Counter submit signal can be used to submit (save) counter value at a specific time
      (for example if you can't determine when the event ends)

* Value interface

    * Each value interface can calculate:

        * Minimal and maximal occurred value
        * Sum and count of all occurred values (SW can then calculate average value)
        * Histogram with custom box count and box with (see :ref:`HISTOGRAMER<histogramer>`)

    * The number of used value interfaces is set via generic parameters
    * Each value interface can have different width
    * Each statistic can be enabled or disabled separately for each interface (to reduce resources)

* Control interface

    * Can be used for custom configuration or status flags and values
    * There is a control output interface and a control input interface

        * CTRLO = output from `DATA_LOGGER`
        * CTRLI = input to `DATA_LOGGER`

    * Each interface can have a custom width (for width 0 is disabled)


Data logger warping component
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. toctree::
   :maxdepth: 1

   mem_logger/readme


Component port and generics description
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


.. vhdl:autoentity:: DATA_LOGGER
   :noautogenerics:


Instance template (simple usage)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block::

    data_logger_i : entity work.DATA_LOGGER
    generic map (
        MI_DATA_WIDTH       => MI_DATA_WIDTH  ,
        MI_ADDR_WIDTH       => MI_ADDR_WIDTH  ,

        CNTER_CNT           => CNTER_CNT      ,
        CNTER_WIDTH         => CNTER_WIDTH
    )
    port map (
        CLK                 => CLK     ,
        RST                 => RST     ,

        CNTERS_INCR         => (
            cnter_incr_2,
            cnter_incr_1,
            cnter_incr_0
        ),

        MI_DWR              => mi_dwr  ,
        MI_ADDR             => mi_addr ,
        MI_BE               => mi_be   ,
        MI_RD               => mi_rd   ,
        MI_WR               => mi_wr   ,
        MI_ARDY             => mi_ardy ,
        MI_DRD              => mi_drd  ,
        MI_DRDY             => mi_drdy
    );

Instance template (full usage)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block::

    data_logger_i : entity work.DATA_LOGGER
    generic map (
        MI_DATA_WIDTH       => MI_DATA_WIDTH  ,
        MI_ADDR_WIDTH       => MI_ADDR_WIDTH  ,

        CNTER_CNT           => CNTER_CNT      ,
        VALUE_CNT           => VALUE_CNT      ,

        CTRLO_WIDTH         => CTRLO_WIDTH    ,
        CTRLI_WIDTH         => CTRLI_WIDTH    ,
        CNTER_WIDTH         => CNTER_WIDTH    ,
        VALUE_WIDTH         => VALUE_WIDTH    ,

        MIN_EN              => MIN_EN         ,
        MAX_EN              => MAX_EN         ,
        SUM_EN              => SUM_EN         ,
        HIST_EN             => HIST_EN        ,

        SUM_EXTRA_WIDTH     => SUM_EXTRA_WIDTH,
        HIST_BOX_CNT        => HIST_BOX_CNT   ,
        HIST_BOX_WIDTH      => HIST_BOX_WIDTH ,
        CTRLO_DEFAULT       => CTRLO_DEFAULT
    )
    port map (
        CLK                 => CLK     ,
        RST                 => RST     ,
        RST_DONE            => rst_done,
        SW_RST              => sw_rst  ,

        CTRLO               => ctrlo   ,
        CTRLI               => ctrli   ,

        CNTERS_INCR         => (
            cnter_incr_2,
            cnter_incr_1,
            cnter_incr_0
        ),
        CNTERS_DIFF         => (
            cnter_diff_2 &
            cnter_diff_1 &
            cnter_diff_0
        ),
        CNTERS_SUBMIT       => (
            cnter_submit_2,
            cnter_submit_1,
            cnter_submit_0
        ),

        VALUES_VLD          => (
            value_vld_2,
            value_vld_1,
            value_vld_0
        ),
        VALUES              => (
            value_2 &
            value_1 &
            value_0
        ),

        MI_DWR              => mi_dwr  ,
        MI_ADDR             => mi_addr ,
        MI_BE               => mi_be   ,
        MI_RD               => mi_rd   ,
        MI_WR               => mi_wr   ,
        MI_ARDY             => mi_ardy ,
        MI_DRD              => mi_drd  ,
        MI_DRDY             => mi_drdy
    );


Control SW
^^^^^^^^^^

Folder ``data_logger/sw/`` contains ``Python3`` package that provides:

* Module for basic interaction with ``DATA_LOGGER``
* Modules for ``DATA_LOGGER`` wraps like ``MEM_LOGGER``
* Simple graph generator based on `matplotlib` library
* Simple PDF / Markdown report generator
* Common tools

Package can be installed using this command:

* You also need to install ``python nfb`` package

.. code-block::

    cd data_logger/sw
    python3 setup.py install --user


MI address space
^^^^^^^^^^^^^^^^

.. code-block::

    0x0000: CTRL REG
            0: sw rst
            1: rst done
    0x0004: STATS REG
    0x0008: INDEX REG
    0x000C: SLICE REG
    0x0010: HIST REG
    0x0014: VALUE REG


* ``CTRL REG`` ... configuration bits
* ``STATS REG`` ... selects statistics

    * ``0`` ... ``CNTER_CNT``
    * ``1`` ... ``VALUE_CNT``
    * ``2`` ... ``MI_DATA_WIDTH``
    * ``3`` ... ``CTRLO_WIDTH``
    * ``4`` ... ``CTRLI_WIDTH``
    * ``5`` ... ``CNTER_WIDTH``
    * ``6`` ... ``VALUE_WIDTH (i)``
    * ``7`` ... ``VALUE_ENs (i)``

        * ``0``.... ``MIN_EN``
        * ``1``.... ``MAX_EN``
        * ``2``.... ``SUM_EN``
        * ``3``.... ``HIST_EN``

    * ``8`` ... ``SUM_EXTRA_WIDTH (i)``
    * ``9`` ... ``HIST_BOX_CNT (i)``
    * ``10``... ``HIST_BOX_WIDTH (i)``
    * ``11``... ``ctrlo``
    * ``12``... ``ctrli``
    * ``13``... ``cnter value (i)``

        * Also use for value interface counters (``CNTER_CNT + VALUE_CNT`` counters)

    * ``14``... ``value min  (i)``
    * ``15``... ``value max  (i)``
    * ``16``... ``value sum  (i)``
    * ``17``... ``value hist (i)``

* ``INDEX REG``... selects value for multi-value statistics `(i)`
* ``SLICE REG``... selects MI width slice for statistics with larger data width
* ``HIST REG``... selects histogram box (write to this register will initiate read request to `HISTOGRAMMER`)
* ``VALUE REG``... register with the requested value
