.. _data_logger:

Data Logger
===========

The **Data Logger** logs statistics about specific events and exposes them on the MI bus.
A simple usage example can be found in the :ref:`MEM_LOGGER <mem_logger>` component.

Key Features
------------

Counter Interface
^^^^^^^^^^^^^^^^^

* Each counter tracks occurrences of an event, clock cycles, etc.
* Number of counter interfaces is configurable via generic parameters.
* All counters share the same width (width is configurable and can be even wider than the MI bus).
* On overflow the counter saturates at its maximum value.
* Custom increment value (default: ``1``).
* Optional ``submit`` signal to latch the current value at a specific moment
  (e.g. when the end of an event cannot be detected immediately).

Value Interface
^^^^^^^^^^^^^^^

Each value interface can compute:

* Minimum and maximum observed value
* Sum and count of all values (average can be calculated in software)
* Histogram with configurable number of bins and bin width
  (see :ref:`HISTOGRAMER <histogramer>`)

Configuration options per interface:

* Number of value interfaces set via generics
* Individual data width per interface
* Each statistic (min/max, sum/count, histogram) can be independently enabled/disabled
  to save resources

Control Interface
^^^^^^^^^^^^^^^^^

Used for custom configuration registers or status flags.

* **CTRLO** ... output binary vector from the Data Logger
* **CTRLI** ... input binary vector to the Data Logger

Both interfaces support arbitrary widths; width ``0`` disables the interface.

Data Logger Wrapping Components
-------------------------------

.. toctree::
   :maxdepth: 1

   mem_logger/readme


Component port and generics description
---------------------------------------

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
----------

Folder ``ndk-fpga/python/ofm/`` contains following ``Python`` packages for ``DataLogger``:

* ``data_logger`` ... basic interaction with ``DATA_LOGGER``
* ``mem_logger`` ... basic interaction with ``MEM_LOGGER``
* ``logger_stats`` ... structured loading of ``DATA_LOGGER`` statistics (multiple ``DATA_LOGGERS`` can be organized in tree hierarchy)
* ``graph_tools`` ... simple plot functions for statistics from ``logger_stats``

**Installation steps**

* Install **NFB python package**

  * See: `ndk-sw <https://github.com/CESNET/ndk-sw?tab=readme-ov-file>`_

* Install **Open FPGA Modules python package**

  * It includes ``data_logger, mem_logger, logger_stats, graph_tools`` packages
  * See: `ndk-fpga/python/ofm <https://github.com/CESNET/ndk-fpga/tree/devel/python/ofm>`_

**Example usage** of ``logger_stats`` (for more usage see `mem_logger/mem_logger.py`):

.. code-block::

    from ofm.comp.debug.data_logger.data_logger import DataLogger
    import ofm.comp.debug.data_logger.logger_stats as Stats

    def create_stats():
        # Create DataLoggers
        # You can specify:
        # * Card device (dev='/dev/nfb1')
        # * MI bus index (when multiple DataLoggers are used)
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

    # Now you can load / print / save all statistics with just one command
    stats.load()
    print(stats.to_str())
    stats.save('stats.npz')


Example usage of ``graph_tools``:


.. code-block::

    from ofm.comp.debug.data_logger.graph_tools import load_data, plot_counter, plot_value, plot_value_2d
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
----------------

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
