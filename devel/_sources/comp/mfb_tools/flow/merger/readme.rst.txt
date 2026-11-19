.. _mfb_merger:

MFB Merger Gen
--------------

.. vhdl:autoentity:: MFB_MERGER_GEN

Using STORED_EOF_EN and PKT_SIZE_MAX parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

With ``STORED_EOF_EN = True``, an input passes an MVB word to the arbitration only when the EOFs
of all frames that this word announces are already in the input MFB FIFO. A granted frame then
needs no data that are not stored yet. The merger counts the EOFs in each input MFB FIFO itself.

Use this mode when the RX inputs depend on each other. An example is a source that sends
packets to two mergers through one splitter. The order of the frames follows the headers, and
the headers can come long before their frames. A merger that waits in the middle of a packet
can stop this source. The source can then stop the other merger.

``STORED_EOF_EN = True`` requires ``IN_MFB_FIFO_EN = True``. Each input MFB FIFO must hold
``MVB_ITEMS`` packets of ``PKT_SIZE_MAX`` items, so that a full FIFO always contains the EOFs
of the next MVB word. Set also ``IN_MVB_FIFO_EN = True``. Without the input MVB FIFO,
``RX_MVB_DST_RDY`` depends on ``RX_MVB_VLD`` and ``RX_MVB_PAYLOAD`` through a longer
combinational path.

MFB Merger Flat
---------------

.. vhdl:autoentity:: MFB_MERGER_FLAT

MFB Merger
----------

.. vhdl:autoentity:: MFB_MERGER
