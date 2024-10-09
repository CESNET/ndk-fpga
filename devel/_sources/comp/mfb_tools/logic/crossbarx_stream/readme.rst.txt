.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Daniel Kondys <kondys@cesnet.cz>
.. SPDX-License-Identifier: BSD-3-Clause

.. _crossbarx_stream:

CrossbarX Stream
----------------

.. vhdl:autoentity:: CROSSBARX_STREAM


Block diagram
^^^^^^^^^^^^^

.. _cx_stream_diag:

.. image:: docs/cx_stream.svg
      :align: center
      :width: 100 %
      :alt:

Operations
^^^^^^^^^^

#. Discarding : discards come with EOFs. Therefore, they are first transferred from the RX Buffer through the CX Stream to the TX Buffer, where they are overwritten by the next transaction.
#. Gap insertion : the Packet Planner component (PP) takes care of this.
#. Shrinking and extending logic : the Length and RX Buffer RD address and TX Buffer WR address are adjusted appropriately, before and after the PP.

      * Shrinking: decrease the length only before the PP. When shrinking from the front, also adjust the RX Buffer RD address.
      * Extending: increase the length before the PP and decrease it after the PP. The increased length is propagated to the TX Buffer in metadata. When extending at the front, also adjust the TX Buffer WR address.
