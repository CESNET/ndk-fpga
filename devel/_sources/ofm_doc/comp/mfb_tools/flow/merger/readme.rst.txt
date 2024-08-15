.. _mfb_merger:

MFB Merger
----------

.. vhdl:autoentity:: MFB_MERGER

There are three variants of MFB Merger:

#. MFB Merger Full

    Merges two input MVB+MFB interfaces in one output interface.
    Only contains 1 input register for each input interface and 1 output register.
    Has lower throughput compared to the OLD MFB Merger architecture,
    but much lesser resource consumption.
    This is the preffered architecture for this unit!

#. MFB Merger Gen

    MFB+MVB bus merger with generic number of inputs

#. MFB Merger Old

    Merges two input MVB+MFB interfaces in one output interface
    Contains input FIFOs and output PIPEs.
    This architecture has not been verified, as it is not supposed to be used.
    Use architecture FULL instead!
