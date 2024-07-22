FlowTest Sequence
=================

FlowTest Sequence uses `FlowTest ft-generator <https://github.com/CESNET/FlowTest/tree/main/tools/ft-generator>`_ to generate and run a PCAP file based on configuration and profile.
The configuration and profile are described in the FlowTest ft-generator repository.

Sequence parameters
-------------------

Configuration generation
^^^^^^^^^^^^^^^^^^^^^^^^

* **generated_config** is an on/off switch determining whether the sequence will generate a new configuration file located at **config_filepath** or use a user-provided file at **config_filepath**.

.. admonition:: Warning
    :class: warning

    If **generated_config** is *on*, the file at **config_filepath** will be overwritten! Be careful not to overwrite something you didn't want!

* **Default is on**.

* You can also optionally provide a configuration that will override the default values of the configuration generator constants. This configuration must be a JSON file located at **config_generator_config_filepath**.
  You can find these constants at the beginning of **config_generator.py**. The constants reflect options provided via a YAML configuration file described in the generator repository.

    * **LAYER_MAX_NUMBER** is the maximum number of layers in the layer list.

    * **LAYER_TYPES** is the list of possible layer types. **Don't change it!**

    * **ENCAPSULATION_ELEMENT_MAX_NUMBER** is the maximum number of elements in the encapsulation list.

    * **GENERATED_IPv4_RANGE_MAX_NUMBER** is the maximum number of generated IPv4 addresses.

    * **GENERATED_IPv6_RANGE_MAX_NUMBER** is the maximum number of generated IPv6 addresses.

    * **GENERATED_MAC_RANGE_MAX_NUMBER** is the maximum number of generated MAC addresses.

    .. admonition:: Note
      :class: note

      **GENERATED_-_RANGE_MAX_NUMBER** parameters are disabled by default *(0)*. The generator uses sequence-generated addresses passed as arguments (e.g. *--ipv4*).

    * **IPv4_PREFIX_MIN** is the minimum possible prefix for generated IPv4 addresses.

    * **IPv4_PREFIX_MAX** is the maximum possible prefix for generated IPv4 addresses.

    * **IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MIN** is the minimum value of **min_packet_size_to_fragment** for IPv4 parameter (see generator repository)

    * **IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MAX** is the maximum value of **min_packet_size_to_fragment** for IPv4 parameter (see generator repository)

    * **IPv6_PREFIX_MIN** is the minimum possible prefix for generated IPv6 addresses.

    * **IPv6_PREFIX_MAX** is the maximum possible prefix for generated IPv6 addresses.

    * **IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MIN** is the minimum value of **min_packet_size_to_fragment** for IPv6 parameter (see generator repository)

    * **IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MAX** is the maximum value of **min_packet_size_to_fragment** for IPv6 parameter (see generator repository)

    * **MAC_PREFIX_MIN** is the minimum possible prefix of generated MAC addresses.

    * **MAC_PREFIX_MAX** is the maximum possible prefix of generated MAC addresses.

    * **PACKET_MIN_SIZE** is the minimum size of packets.

    * **PACKET_MAX_SIZE** is the maximum size of packets.

    * **PACKET_SIZE_MIN_STEP** is the minimum size of **packet_size_probabilities** ranges (see generator repository)

    * **PACKET_SIZE_MAX_STEP** is the maximum size of **packet_size_probabilities** ranges (see generator repository)

    * **MAX_FLOW_INTER_PACKET_GAP** is the **max_flow_inter_packet_gap** parameter (see generator repository)

    * **MANDATORY_IPv4_ADDRESS_RANGES** is the list of user-defined IPv4 addresses. Use this if you want to generate specific IPv4 addresses.

    * **MANDATORY_IPv6_ADDRESS_RANGES** is the list of user-defined IPv6 addresses. Use this if you want to generate specific IPv6 addresses.

    * **MANDATORY_MAC_ADDRESS_RANGES** is the list of user-defined MAC addresses. Use this if you want to generate specific MAC addresses.

Profile generation
^^^^^^^^^^^^^^^^^^

* **generated_profile** is an on/off switch determining whether the sequence will generate a new profile file located at **profile_filepath** or use a user-provided file at **profile_filepath**.

.. admonition:: Warning
    :class: warning

    If **generated_profile** is *on*, the file at **profile_filepath** will be overwritten! Be careful not to overwrite something you didn't want!

* **Default is on**.

* You can also optionally provide a configuration that will override the default values of the profile generator constants. This configuration must be a JSON file located at **profile_generator_config_filepath**.
  You can find these constants at the beginning of **profile_generator.py**. The constants reflect options provided via a CSV profile file described in the generator repository.

    * **START_TIME_MIN** is the minimum possible start time of a flow.

    * **START_TIME_MAX** is the maximum possible start time of a flow.

    * **END_TIME_MIN** is the minimum possible end time of a flow.

    * **END_TIME_MAX** is the maximum possible end time of a flow.

    * **PACKETS_MIN_NUMBER** is the minimum possible number of packets in the forward direction.

    * **PACKETS_MAX_NUMBER** is the maximum possible number of packets in the forward direction.

    * **BYTES_PER_PACKET_MIN_NUMBER** is the minimum possible number of bytes per packet in the forward direction.

    * **BYTES_PER_PACKET_MAX_NUMBER** is the maximum possible number of bytes per packet in the forward direction.

    * **BYTES_MIN_NUMBER** is the minimum possible number of bytes in the forward direction.

    * **BYTES_MAX_NUMBER** is the maximum possible number of bytes in the forward direction.

    * **PACKETS_REV_MIN_NUMBER** is the minimum possible number of packets in the reverse direction.

    * **PACKETS_REV_MAX_NUMBER** is the maximum possible number of packets in the reverse direction.

    * **BYTES_PER_PACKET_REV_MIN_NUMBER** is the minimum possible number of bytes per packet in the reverse direction.

    * **BYTES_PER_PACKET_REV_MAX_NUMBER** is the maximum possible number of bytes per packet in the reverse direction.

    * **BYTES_REV_MIN_NUMBER** is the minimum possible number of bytes in the reverse direction.

    * **BYTES_REV_MAX_NUMBER** is the maximum possible number of bytes in the reverse direction.

    * **RECORD_MIN_NUMBER** is the minimum possible number of flows.

    * **RECORD_MAX_NUMBER** is the maximum possible number of flows.

Example configurations
----------------------

.. admonition:: Note
    :class: note

    Parameters in a JSON configuration are case-insensitive and can be provided in any order.

Configuration generator configuration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: json

  {
    "MANDATORY_IPv4_ADDRESS_RANGES": [
      "1.1.1.1/1",
      "192.168.1.1/30",
      "255.255.255.255/32"
    ],
    "LAYER_MAX_NUMBER": 4,
    "IPV4_PREFIX_MIN": 28,
    "ipv4_prefix_max": 32,
    "MAX_flow_INTER_packet_GAP": 32
  }

Profile generator configuration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: json

  {
    "START_TIME_MIN": 412,
    "PACKETS_REV_MIN_NUMBER": 10,
    "record_min_number": 50,
    "RECORD_MAX_number": 100
  }
