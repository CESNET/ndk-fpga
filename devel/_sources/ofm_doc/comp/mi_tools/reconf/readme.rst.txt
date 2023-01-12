.. _mi_reconfigurator:

MI Reconfigurator
-----------------

The MI Reconfigurator can be used to modify the width of MI interface.
Both RX and TX data width has to be a power of 2 and at least 8 bits.

Architecture
^^^^^^^^^^^^

The architecture has 3 different shapes depending on the way of reconfiguration:

#. RX width == TX width

    When the data width is not being changed at all, the component is reduced to direct signal connections.

#. RX width < TX width

    When the data width is being increased the following has to be done:

    The target address on the MI bus always has to be aligned to a whole MI data word.
    (e.g.: when using 4-byte words, the lowest log2(4) bits of the addres have to be 0.)
    When converting to a wider bus, the valid data have to be shifted to the correct position in the TX DWR and the RX ADDR has to be rounded down.
    The data validity is then signaled by the TX BE (Byte Enable).

    The same has to be done for read requests as well, only the shifting is done the other way around for the TX DRD.
    (The unit has to remember the lowest bits of the original request to shift the DRD correctly.)

.. image:: doc/mi_reconfigurator_dwr_up.svg
      :align: center
      :width: 60 %
      :alt:

#. RX width > TX width

    In this case, each RX request might require to produce multiple TX requests.
    This means, that each rquest might take multiple cycles to process.
    To reduce the required time the unit only propagates valid parts of the requests based on the RX BE value and *does not generate any tX requests with TX BE == 0*.
    The most complicated part here, is processing of read request DRD signals.
    
    In this mode, the component doesn't support execution of multiple parallel requests.

.. image:: doc/mi_reconfigurator_dwr_down.svg
      :align: center
      :width: 60 %
      :alt:
