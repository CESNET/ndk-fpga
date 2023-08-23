.. _ndk_f-tile_multirate:

F-Tile Multirate IP 
===================

Implemented IP cores 
--------------------

Right now, you can use two designs with Multirate IP. These designs have optimized parameters, so you do not need to change anything.
These designs are 100GE and 25GE, the individual profiles that can be set are listed in :ref:`Tab. 1 <Tab. 1 F-Tile_Multirate IPs variants>`.
If you want to make a build with Multirate IP, check the ``Makefile`` file for agi-fh400g, there are pseudo names for each Multirate IP core.

Build tips
----------

The first step is to make a build. If an error during the build occurs, here are a few tips to help you to fix them. 
If you have a problem during the build with Timing analysis and it seems that it could be because of asynchronous clk signals, look into the ``timing.sdc`` file. There is the declaration of asynchronous clocks for both Multirate IP cores.
If you have a problem with the Profile ID setup for Dynamic Reconfiguration, look into ``multirate.qsf``. There is the declaration of profiles for both types of IP cores (100G and 25G) and it is set by its setup (the order of profiles when the IP was generated). These assignments allow you to set the order of all profiles (from 0 to ...) for all IP cores.
If you have other problems, look into Intel's documentation: :ref:`Intel F-Tile Ethernet Multirate Intel FPGA IP User Guide <https://cdrdv2-public.intel.com/773503/ug-714307-773503.pdf>` and :ref:`Intel F-Tile Dynamic Reconfiguration Suite Intel FPGA IP User Guide <https://www.intel.com/programmable/technical-pdfs/711009.pdf>`.

.. list-table:: Tab. 1 F-Tile_Multirate IPs variants
    :align: center
    :widths: 10 25 25 30
    :header-rows: 1

    * - IP speed
      - reconfigurated IP speed
      - Profile number
      - FEC-Type
    * - 100GE
      - 100GE
      - 1
      - FEC-91
    * - 100GE
      - 100GE
      - 2
      - NO-FEC
    * - 25GE
      - 25GE
      - 1
      - NO-FEC
    * - 25GE
      - 25GE
      - 2
      - FEC-91
    * - 25GE
      - 25GE
      - 3
      - FEC-134
    * - 25GE
      - 10GE
      - 4
      - NO-FEC

|

Switching profiles
------------------

Python script named ``profile_swap.py`` was made for swapping profiles.
There are five parameters, which have to be set to change the speed or type of FEC. These parameters are:

- ``-s_ch`` Start_channel - represents which first IP from the range of IPs that you want to change the position of. The first IP is ``0``.
- ``-ch``   Channels - indicates the range from the _start channel_ that you want to change. There is a treatment in case of a non-valid range choice.
- ``-s_p``  Start_profile - this parameter needs to be set to the profile, which was applied as the last default profile after the build is ``1``.
- ``-e_p``  End_profile - indicates a profile to which you want to change the IP core. :ref:`Tab. 1 <Tab. 1 F-Tile_Multirate IPs variants>` lists possible variants.
- ``-sp``   Speed - represents the speed of the implemented IP core, the values of speeds that you can use are shown in the _help_ also in the script.
- ``-d``    Device - represents the device, which is used for the implemented design. The default value is ``0``.


