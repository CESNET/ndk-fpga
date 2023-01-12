.. readme.rst: Documentation of single component
.. Copyright (C) 2022 CESNET z. s. p. o.
.. Author(s): Daniel Kondys <kondys@cesnet.cz>
..
.. SPDX-License-Identifier: BSD-3-Clause

.. _mfb_generator:

MFB Generator
-------------

.. vhdl:autoentity:: MFB_GENERATOR_MI32

Distribution examples
^^^^^^^^^^^^^^^^^^^^^

- 0x000000: Do not distribute frames
- 0xff0001: Distribute frames to all available channels
- 0x070401: Distribute frames to channels 4 to 7
- 0xff0002: Distribute frames to all even channels (0, 2, 4, ...)
- 0x050501: Send all frames to channel number 5 only
