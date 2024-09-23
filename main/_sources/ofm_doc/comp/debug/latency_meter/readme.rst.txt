.. _latency_meter:

Latency meter
-------------

Latency meter is used to measure the duration of a specific event.

Key features
^^^^^^^^^^^^

* Measures the number of ticks between the start and the end of a given event
* Multiple parallel events can be measured
* Zero latency events can be measured (start and end occurs at the same time)

Component port and generics description
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


.. vhdl:autoentity:: LATENCY_METER
   :noautogenerics:

Instance template
^^^^^^^^^^^^^^^^^

.. code-block::

    latency_meter_i : entity work.LATENCY_METER
    generic map (
        DATA_WIDTH              => DATA_WIDTH,
        MAX_PARALEL_EVENTS      => MAX_PARALEL_EVENTS,
        DEVICE                  => DEVICE
    )
    port map (
        CLK                     => CLK,
        RST                     => RST,
        START_EVENT             => start_event,
        END_EVENT               => end_event,
        LATENCY_VLD             => latency_vld,
        LATENCY                 => latency
    );
