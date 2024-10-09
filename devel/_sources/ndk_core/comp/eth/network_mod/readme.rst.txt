.. _ndk_network_mod:

NETWORK MODULE
--------------

Typical Configurations
^^^^^^^^^^^^^^^^^^^^^^

.. list-table::
    :align: center
    :header-rows: 1

    * - ETH_CORE_ARCH
      - E_TILE
      - F_TILE
      - CMAC
    * - ETH_PORT_SPEED
      - 100, 25, 10
      - 400, 200, 100, 50, 40, 25, 10
      - 100
    * - ETH_PORT_CHAN (for each speed)
      - 1, 4, 4
      - 1, 2, 4, 8, 2, 8, 8
      - 1
    * - LANES
      - 4
      - 8
      - 4
    * - MFB Configuration
      - 1, 8, 8, 8 (512b)
      - 4, 8, 8, 8 (2048b)
      - 1, 8, 8, 8 (512b)

Verification Plan
^^^^^^^^^^^^^^^^^

It is necessary to test all supported Ethernet IP architectures (E-Tile, CMAC,...) and their supported speeds/channels.

.. list-table::
    :align: center
    :header-rows: 1

    * - ID
      - Description
      - Requirement level
      - Checked by
      - Status
      - Test name
    * - 1
      - Dropped packets (overflow, unmasked errors).
      - Obligatory
      - Func. cover
      - TBD
      - All tests
    * - 2
      - Checking the MAC address according to the values written in the configurable TCAM.
      - Obligatory
      - Func. cover
      - TBD
      - All tests
    * - 3
      - Test checking the setting of the minimum and maximum packet length and discarding packets outside the range.
      - Obligatory
      - Func. cover
      - TBD
      - All tests
    * - 4
      - Read out (via MI) and check statistics in RX/TX MAC.
      - Obligatory
      - Func. cover
      - TBD
      - All tests
    * - 5
      - Maximum speed test (output does not brake and input goes full speed), 100% throughput is expected for all packet lengths.
      - Obligatory
      - Func. cover
      - TBD
      - test::speed

Entity Docs
^^^^^^^^^^^

.. vhdl:autoentity:: NETWORK_MOD