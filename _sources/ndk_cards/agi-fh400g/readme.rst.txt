.. _card_400g1:

XpressSX AGI-FH400G (400G1)
---------------------------

- XpressSX AGI-FH400G by CESNET & REFLEX CES
    - Intel Agilex I-Series FPGA (1x F-Tile, 3x R-Tile)
    - FPGA Part Number (ES Silicon) = ``AGIB027R29A1E2VR0``
    - FPGA Part Number (Production Silicon) = ``AGIB027R29A1E2V``
    - `XpressSX AGI-FH400G Website <https://www.reflexces.com/pcie-boards/intel-agilex-soc/xpresssx-agi-fh400g-agilex-soc-full-height-half-length-pcie-board>`_

.. warning::

   This page is still work in progress!

Build instructions
^^^^^^^^^^^^^^^^^^

- Go to ``build/agi-fh400g/`` folder in application repository.
- Check or modify ``user_const.tcl`` file, where you can change the firmware configuration.
- Run firmware build in Quartus by ``make`` command.
    - Use ``make 400g1`` command for firmware with 1x400GbE (default).
    - Use ``make 200g2`` command for firmware with 2x200GbE.
    - Use ``make 100g4`` command for firmware with 4x100GbE.
    - Use ``make 50g8`` command for firmware with 8x50GbE.
    - Use ``make 40g2`` command for firmware with 2x40GbE.
    - Use ``make 25g8`` command for firmware with 8x25GbE.
    - Use ``make 10g8`` command for firmware with 8x10GbE.
- After the build is complete, you will find bitstream ``my_bitstream.sof`` in the same folder.

.. note::

    To build firmware, you must have Quartus Prime Pro installed, including a valid license.

Board Test Scripts
^^^^^^^^^^^^^^^^^^

The NDK design enables easy testing of the FPGA card. The design includes several generators and switchable loopback paths (usually part of :ref:`the Gen Loop Switch (GLS) <gls_debug>` unit). A simplified diagram showing the testing capabilities can be found below.

.. image:: doc/ndk_loopback.drawio.svg
    :align: center
    :width: 100 %

**Prerequisites**

- The card must be connected to a linux server.
- The NDK software package must be installed on this server.
- NDK driver must be in debug mode (mi_debug).
- The FPGA card must boot the NDK firmware.
- You must have Python 3 including the pytest framework installed: ``pip3 install --user pytest pytest-depends pytest-html``

The test scripts themselves are written in `Python 3 <https://www.python.org/>`_ and use `the Pytest framework <https://docs.pytest.org/en/stable/>`_. This makes it possible to run the test with a single command, see example:

.. code:: bash

    $ pytest --html=test_pcie.html --self-contained-html card/400g1/bts/test_pcie.py

The whole test takes approximately 14 minutes. The test script displays test results and generates an html file containing a detailed description of the test results.

.. warning::

    The test script requires an NDK driver in debug mode! To enable debug mode, you must first remove the driver with the command “sudo modprobe -r nfb” and then add it with the correct flag: “sudo modprobe nfb mi_debug=1”.

Ethernet Interface
^^^^^^^^^^^^^^^^^^

This card has one QSFP-DD cage (ports). It is connected to the FPGA via 8 high-speed serial lines supporting up to 56 Gbps. QSFP-DD cage is connected to an F-Tile that contains Ethernet Hard IP supporting the following speeds: ``1x400GbE, 2x200GbE, 4x100GbE, 8x50GbE, 2x40GbE, 8x25GbE, 8x10GbE``. F-Tile Hard IPs are instantiated in Network Module, which provides Ethernet communication to and from the Application core. The architecture of the Network Module :ref:`is described here <ndk_intel_net_mod>`.

.. note::

    Not all Ethernet Hard IP configurations are already available or tested in NDK.
