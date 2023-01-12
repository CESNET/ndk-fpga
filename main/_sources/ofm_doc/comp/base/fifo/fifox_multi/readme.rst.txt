.. _fifox_multi:

FIFOX Multi
-----------

.. vhdl:autoentity:: FIFOX_MULTI

Block diagram
^^^^^^^^^^^^^

.. Path relative to local directory for Gitlab preview
.. image:: doc/fifox_multi.svg
      :width: 100 %
      :alt:

Write interface behavior
^^^^^^^^^^^^^^^^^^^^^^^^

The write interface allows you to write ``0`` to :vhdl:genconstant:`WRITE_PORTS <fifox_multi.write_ports>` items in each clock cycle. Valid input items are marked by setting the corresponding bit of :vhdl:portsignal:`WR <fifox_multi.wr>` to ``'1'``.

The write requests are only performed when signal :vhdl:portsignal:`FULL <fifox_multi.full>` has value ``'0'``. When ``FULL`` is ``'0'``, no items can be written.

In case of multiple simultaneous writes the item on port ``0`` will be placed as the first in the FIFO and the item on port ``WRITE_PORTS-1`` as the last.

Read interface behavior
^^^^^^^^^^^^^^^^^^^^^^^

The read interface allows you to read ``0`` to :vhdl:genconstant:`READ_PORTS <fifox_multi.read_ports>` items in each clock cycle.
**Simultaneous read requests must be continuous from index 0 up. You cannot read items out-of-order.**

Example::
    For ``READ_PORTS == 4``, ``RD[4-1 : 0]`` supports values ``"0000"``, ``"0001"``, ``"0011"``, ``"0111"`` and ``"1111"``.
    All other permutations of ``RD`` are forbidden and can lead to undefined behavior of the component!

Port :vhdl:portsignal:`EMPTY <fifox_multi.empty>` works as a "not valid" flag for each output Item.

**When generic** :vhdl:genconstant:`SAFE_READ_MODE <fifox_multi.safe_read_mode>` **is set to** ``false`` **, the user can only read from read ports, where** ``EMPTY[i] == '0'`` **.**

When generic :vhdl:genconstant:`SAFE_READ_MODE <fifox_multi.safe_read_mode>` is set to ``true``, reading from an empty port will have no effect.
