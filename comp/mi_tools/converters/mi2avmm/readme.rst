.. _mi2avmm:

MI2AVMM
-------

.. vhdl:autoentity:: MI2AVMM

Read :ref:`MI bus specification<mi_bus>` for more information on the MI bus.

Specification
^^^^^^^^^^^^^

Both interfaces use common clock and reset signals.
AVMM interface does not support *debugaccess*, optional signals (*response*, *writeresponsevalid*), *lock* for multiple hosts and burst mode signals (*burstcount*, *beginbursttransfer*).
Pipelined read transfers are possible with *readdatavalid* signal.
According to the Avalon-MM specification, there must be at least one cycle of latency between acceptance of the *read* signal and assertion of *readdatavalid* (in opposite to MI bus DRDY signal with possible 0 cycle latency).
*waitrequest* signal is asserted when the component is unable to accept data, thus the data must be kept constant until the signal is deasserted (MI bus ARDY signal negation).

.. warning::
   The *waitrequestAllowance* property is the number of transfers accepted after assertion of *waitrequest* signal. The only supported value of this property is 0.

.. warning::
   This component only supports data with the same width on both sides (32 bits by default).
   These are addressed as one unit (e.g. when using 32 bit data, byte adresses 0x00 to 0x03 will be on OFFSET[0], 0x04 to 0x07 on OFFSET[1]).

Refer to `Avalon Interface Specification <https://www.intel.com/content/dam/www/programmable/us/en/pdfs/literature/manual/mnl_avalon_spec.pdf>`_ for more information on Avalon-MM interfaces (see section 3).
