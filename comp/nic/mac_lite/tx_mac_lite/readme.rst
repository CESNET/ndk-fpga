.. _tx_mac_lite:

TX MAC LITE
-----------

This component is used to implement the Ethernet MAC layer on the transmitting side.
Thanks to the modular architecture (TX MAC LITE + Adapter), it can be connected to a supported ETH Hard IP block or implement the MAC layer separately.
The implementation may include differences from the Ethernet standard.

Architecture
^^^^^^^^^^^^

The TX MAC LITE checks the length of the input frames, if it is less than 60B, these frames are discarded.
TX MAC LITE may optionally contain subcomponents that are used to calculate and insert a CRC into the frame being sent.
In cases where the module must insert a CRC or generate inter-packet gaps, the Spacer (CrossbarX Stream) component is used as the main buffer.
In case these operations (CRC, IPG) are performed by Ethernet HARD IP, the :ref:`MFB_PD_ASFIFO <mfb_pd_asfifo>` component is used as the main buffer.
The whole module can be controlled by SW using MI registers (see chapter Register Map).

.. image:: doc/tx_mac_lite.drawio.svg
      :align: center
      :width: 100 %

**Description of TX MAC LITE submodules:**

- **ADDR DEC** - controls the whole module through MI registers
- **Stats Unit** - contains statistical counters accessible through MI registers
- **Length Check** - calculates and checks the minimal length of the Ethernet frame
- **CRC Gen** - calculate the CRC of the Ethernet frame before sent (optional, it is not available in OFM repository, extra license required)
- **CRC Insert** - insert the CRC to the Ethernet frame before sent (optional)
- **MFB PD ASFIFO** - store and forward buffer is used to store the Ethernet frame, use when it is not necessary to generate a CRC and/or inter packet gaps (IPG), for example, in cases where the CRC is inserted by Ethernet Hard IP
- **Spacer** - store and forward buffer is used to store the Ethernet frame and generate space for inserting the CRC and IPG according to the Ethernet standard

Adapter
^^^^^^^

The adapter allows you to connect the TX MAC LITE to various variants of the PCS/PMA layer of the Ethernet or various Ethernet Hard IPs.
The main task of the adapter is to convert the selected input bus to the MFB bus.
Currently, several variants of the adapter are implemented:

- **UMII Adapter** - connects Ethernet PCS/PMA layer with MII interface for various speeds (XGMII, XLGMII, CDGMII,...)
- **CMAC Adapter** - connects CMAC Hard IP, which is used in Xilinx UltraScale+ FPGA for 100 Gbps Ethernet (Uses MFB not LBUS!)
- **AVST Adapter** - connects E-Tile Hard IP, which is used in Intel Stratix 10 and Agilex FPGA for up to 100 Gbps Ethernet
- **MAC Segmented Adapter (WIP)** - connects F-Tile Hard IP, which is used in Intel Agilex FPGA for up to 400 Gbps Ethernet

Register Map
^^^^^^^^^^^^

TX MAC LITE is off by default, it must be turned on (Enable register) to allow Ethernet frames to be sent.
There are four statistical counters in the address space. You have to sample the counters first and then you can read their content.

.. note::

    If the TX MAC LITE unit is enabled, these counters will have a floating content.
    For this reason, it is necessary to strobe their actual values at the one moment into the counter registers.
    Software tool is then able to read those registers.

======  ==================================================================
Offset  Name of register
======  ==================================================================
0x00    Total Frames Counter - low part (TFCL)
0x04    Sent Octects Counter - low part (SOCL)
0x08    Discarted Frames Counter - low part (DFCL)
0x0C    Sent Frames Counter - low part (SFCL)
0x10    Total Frames Counter - high part (TFCH)
0x14    Sent Octects Counter - high part (SOCH)
0x18    Discarded Frames Counter - high part (DFCH)
0x1C    Sent Frames Counter - high part (SFCH)
0x20    Enable register
0x24    Reserved bits
0x28    Reserved bits
0x2C    Command register
0x30    Status register
======  ==================================================================

**Total Frames Counter - low part (TFCL)**

This is the low part of counter that holds number of all processed frames. (TFC = SFC + DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - low part
====  ===  =============  ======  ==============

**Total Frames Counter - high part (TFCL)**

This is the high part of counter that holds number of all processed frames. (TFC = SFC + DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - high part
====  ===  =============  ======  ==============

**Sent Frames Counter - low part (SFCL)**

This is the low part of counter that holds number of frames that were successfully sent. (SFC = TFC - DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - low part
====  ===  =============  ======  ==============

**Sent Frames Counter - high part (SFCL)**

This is the high part of counter that holds number of frames that were successfully sent. (SFC = TFC - DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - high part
====  ===  =============  ======  ==============

**Sent Octects Counter - low part (SOCL)**

This is the low part of counter that holds number of data octets (bytes) in frames that were successfully sent.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - low part
====  ===  =============  ======  ==============

**Sent Octects Counter - high part (SOCL)**

This is the high part of counter that holds number of data octets (bytes) in frames that were successfully sent.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - high part
====  ===  =============  ======  ==============

**Discarded Frames Counter - low part (SFCL)**

This is the low part of counter that holds number of discarted frames due to being to short (<60B without CRC). (DFC = TFC - SFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - low part
====  ===  =============  ======  ==============

**Discarded Frames Counter - high part (SFCL)**

This is the high part of counter that holds number of discarted frames due to being to short (<60B without CRC). (DFC = TFC - SFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value - high part
====  ===  =============  ======  ==============

**Enable register**

The value stored in this register determines whether the TX MAC LITE unit is enabled or not.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     0    Enable         RW      Assert this bit to change the TX MAC LITE status to 'enabled'. Clear this bit to change the TX MAC LITE status to 'disabled'. As soon as the TX MAC LITE status is set to 'enabled' the TX MAC LITE unit starts working.
1     31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

**Command register**

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     7    Command        W       Write a command into this register.
8     31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

Command definition:

- 0x01 - CMD STROBE COUNTERS: Writing this constant into the command register will cause that the current frame counters' values will be stored into the frame counter registers at the same moment.
- 0x02 - CMD RESET COUNTERS: Writing this constant into the command register will cause that the frame counters will be reset.

**Status register**

====  ===  =================  ======  ==============
From  To   Name               Access  Description
====  ===  =================  ======  ==============
0     0    Enable status       R       When is '1' TX MAC LITE is enabled else TX MAC LITE is disabled.
1     1    CRC insert status   R       When is '1' TX MAC LITE does not insert CRC into frames else TX MAC LITE inserts CRC into frames.
2     3    Reserved            R       Reserved bits.
4     6    Obsolete            R       Ignore these bits.
7     31   Reserved            R       Reserved bits.
====  ===  =================  ======  ==============

Ports and Generics
^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: TX_MAC_LITE
