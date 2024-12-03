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

Folder ``data_logger/sw/`` contains following ``Python3`` packages:

* ``data_logger`` ... basic interaction with ``DATA_LOGGER``
* ``mem_logger`` ... basic interaction with ``MEM_LOGGER``
* ``logger_stats`` ... loading firmware statistics (multiple ``DATA_LOGGERS`` can be organized in tree hierarchy)
* ``graph_tools`` ... simple plot functions for statistics from ``logger_stats``

Package can be installed using this command:

* You also need to install ``python nfb`` package

.. code-block::
    python3 -m pip install --upgrade pip

    # Install nfb:
    cd swbase/pynfb
    python3 -m pip install Cython
    python3 -m pip install .
    cd -

    # Install this package:
    cd data_logger/sw
    python3 -m pip install .

Example usage of ``logger_stats`` (for more usage see `mem_logger/mem_logger.py`):

.. code-block::


    import logger_stats as Stats
    from data_logger.data_logger import DataLogger

    def create_stats():
        # Create DataLoggers
        logger_0 = DataLogger(index=0)
        logger_1 = DataLogger(index=1)

        # Create Stats hierarchy
        stats = Stats.LoggerStats('Example stats')
        stats_0 = Stats.LoggerStats('Logger 0 stats', logger=logger_0)
        stats_1 = Stats.LoggerStats('Logger 1 stats', logger=logger_1)
        stats.add_stat(stats_0)
        stats.add_stat(stats_1)

        # Add basic statistics
        stats_0.add_stat(Stats.Constant(index=7, name='X'))
        stats_0.add_stat(Stats.Counter(index=7, name='Y'))
        stats_0.add_stat(Stats.Value(index=7, name='Z'))

        # FSM state statistic
        def fms_convert(v):
            states = [
                'IDLE',
                ...
            ]
            if v >= len(states):
                return "???"
            else:
                return states[int(v)]

        fsm_format = Stats.FormatDefaultValue(format=Stats.FormatNone)
        stats_1.add_stat(Stats.Value(2, 'FSM states', convert=fms_convert, format=fsm_format))

        # Latency statistic
        FREQ = 200 * 10**6
        time_conv = Stats.ConvertTime(FREQ)
        time_form = Stats.FormatDefaultValue(units='ns')
        stats_1.add_stat(Stats.Value(9, 'Latency', convert=time_conv, format=time_form))

        # Add value statistic which includes multiple commands
        CMDS = [
            'CMD_A',
            ...
        ]
        stats_1.add_stat(Stats.ValueCMD(7, 'Latency of CMDs', cmd_width=2, cmds=CMDS, convert=time_conv, format=time_form))

        # Add multiple counters
        counters = [
            'Counter A',
            ...
        ]
        stats_1.add_stats(
            name='Counters',
            names=counters,
            indexes=list(range(len(counters))),
            constructor=lambda i, n: Stats.Counter(i, n)
        )

    return stats


    stats = create_stats()
    stats.load()
    print(stats.to_str())
    stats.save('stats.npz')


Example usage of ``graph_tools``:

    from graph_tools.graph_tools import load_data, plot_counter, plot_value, plot_value_2d

    stats = load_data('stats.npz')

    node = pd.DataFrame.from_dict(stats['Stats A']['Counters'])
    selected = ['Counter A', 'Counter B']

    # Plot single counter
    plot_counter(node['Counter X'], 'Time', 'Requests', 'Plot title')

    # Plot multiple counters
    plot_counter(node[selected], 'Time', 'Requests', 'Plot title')

    # Plot histogram of the value interface
    plot_value(node['Value A'], 'Time', 'Blocks', 'Title' log=True)

    # Plot 2D histogram of the value interface history
    plot_value_2d(node['Value A'], 'Time', 'Blocks', 'Title' log=True)



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
