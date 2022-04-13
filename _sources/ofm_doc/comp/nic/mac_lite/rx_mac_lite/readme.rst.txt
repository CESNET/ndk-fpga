.. _rx_mac_lite:

RX MAC LITE
-----------

This component is used to implement the Ethernet MAC layer on the receiving side.
Thanks to the modular architecture (RX MAC LITE + Adapter), it can be connected to a supported ETH Hard IP block or implement the MAC layer separately.
The implementation may include differences from the Ethernet standard.

Architecture
^^^^^^^^^^^^

RX MAC LITE contains several components that analyze the received frame (CRC, MAC address, length) and check for errors. The Ethernet frame is stored in the buffer (store and forward), if it does not contain errors, it is sent to the output interface along with the metadata, otherwise the frame is discarded. Some of these components are optional. The whole module can be controlled by SW using MI registers (see chapter Register Map).

.. image:: doc/rx_mac_lite_arch.svg
      :align: center
      :width: 100 %

**Description of RX MAC LITE submodules:**

- **CTRL Unit** - controls the whole module through MI registers
- **Enabler** - enables the receiving of Ethernet frames, if disabled, incoming frames are discarded
- **CRC Cutter** - cuts the CRC of the received Ethernet frame (optional)
- **Length Check** - calculates and checks the length of the received Ethernet frame
- **CRC Check** - checks the CRC of the received Ethernet frame (optional, it is not available in OFM repository, extra license required))
- **MAC Check** - extracts and checks the MAC address of the received Ethernet frame (optional)
- **Time Stamp** - assigns a time stamp to the received Ethernet frame (optional)
- **Error masking** - allows to mask individual errors of the received Ethernet frame
- **Buffer** - store and forward buffer is used to store the received Ethernet frame
- **Stats Unit** - contains statistical counters accessible through MI registers

Adapter
^^^^^^^

The adapter allows you to connect the RX MAC LITE to various variants of the PCS/PMA layer of the Ethernet or various Ethernet Hard IPs.
The main task of the adapter is to convert the selected input bus to the MFB bus.
Currently, several variants of the adapter are implemented:

- **UMII Adapter** - connects Ethernet PCS/PMA layer with MII interface for various speeds (XGMII, XLGMII, CDGMII,...)
- **CMAC Adapter** - connects CMAC Hard IP, which is used in Xilinx UltraScale+ FPGA for 100 Gbps Ethernet (Uses MFB not LBUS!)
- **AVST Adapter** - connects E-Tile Hard IP, which is used in Intel Stratix 10 and Agilex FPGA for up to 100 Gbps Ethernet
- **MAC Segmented Adapter (WIP)** - connects F-Tile Hard IP, which is used in Intel Agilex FPGA for up to 400 Gbps Ethernet
 
Register Map
^^^^^^^^^^^^

It is possible to configure RX MAC LITE on the fly, but if you want to make changes atomically, you should disable RX MAC LITE first.
You can set MAC check mode, RX MAC LITE error mask, minimal and maximal frame length.
After you are done you can enable RX MAC LITE.
You can also write all valid MAC addresses into MAC memory, but the MAC memory can be accessed by software only when the RX MAC LITE is disabled!

You can read number of received, correct, discarded and discarded due to buffer overflow frames or number of correctly received bytes.
You have to sample the counters first and then you can read their content. RX MAC LITE has four frame counters:
Total Received Frames Counter (TRFC), Correct Frames Counter (CFC), Discarded Frames Counter (DFC) and Counter of Frames Discarded due to Buffer Overflow (BODFC) and the byte counter:
Octets Received OK Counter (OROC).

.. note::

    If the RX MAC LITE unit is enabled, these counters will have a floating content.
    For this reason, it is necessary to strobe their actual values at the one moment into the counter registers.
    Software tool is then able to read those registers.

======  ==================================================================
Offset  Name of register
======  ==================================================================
0x00    Total Received Frames Counter - low part (TRFCL)
0x04    Correct Frames Counter - low part (CFCL)
0x08    Discarded Frames Counter - low part (DFCL)
0x0C    Counter of frames discarded due to buffer overflow - low part (BODFCL)
0x10    Total Received Frames Counter - high part (TRFCH)
0x14    Correct Frames Counter - high part (CFCH)
0x18    Discarded Frames Counter - high part (DFCH)
0x1C    Counter of frames discarded due to buffer overflow - high part (BODFCH)
0x20    Enable register
0x24    Error mask register
0x28    Status register
0x2C    Command register
0x30    Minimum frame length allowed
0x34    Frame MTU
0x38    MAC address check mode
0x3C    Octets Received OK Counter - low part (OROCL)
0x40    Octets Received OK Counter - high part (OROCH)
0x80    Memory of available MAC addresses
======  ==================================================================

**Total Received Frames Counter - low part (TRFCL)**

This is the low part of counter that holds number of all arrived frames including those being received at the moment. (TRFC = CFC + DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Correct Frames Counter - low part (CFCL)**

This is the low part of counter that holds number of frames that passed sampling and all controls (was found to be correct) and are forwarded to the RX MAC LITE's output. (CFC = TRFC - DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Discarded Frames Counter - low part (DFCL)**

This is the low part of counter that holds number of frames that did NOT pass sampling or any control (was found to be NOT correct) and are NOT forwarded to the RX MAC LITE's output. (DFC = TRFC - CFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Counter of frames discarded due to buffer overflow - low part (BODFCL)**

This is the low part of counter that holds number of frames that were discarded due to buffer overflow.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Total Received Frames Counter - high part (TRFCH)**

This is the high part of counter that holds number of all arrived frames including those being received at the moment. (TRFC = CFC + DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Correct Frames Counter - high part (CFCH)**

This is the high part of counter that holds number of frames that passed sampling and all controls (was found to be correct) and are forwarded to the RX MAC LITE's output. (CFC = TRFC - DFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Discarded Frames Counter - high part (DFCH)**

This is the high part of counter that holds number of frames that did NOT pass sampling or any control (was found to be NOT correct) and are NOT forwarded to the RX MAC LITE's output. (DFC = TRFC - CFC)

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Counter of frames discarded due to buffer overflow - high part (BODFCH)**

This is the high part of counter that holds number of frames that were discarded due to buffer overflow.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Enable register**

The value stored in this register determines whether the RX MAC LITE unit is enabled or not.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     0    Enable         RW      Assert this bit to change the RX MAC LITE status to 'enabled'. Clear this bit to change the RX MAC LITE status to 'disabled'. As soon as the RX MAC LITE status is set to 'enabled' the RX MAC LITE unit starts working.
1     31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

**Error mask register**

This register specifies which controls will be done over incoming frames. The value stored in this register determines which kinds of errors cause the frame discarding.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     0    ADAPTER_ERROR  RW      This bit signals whether the error notified by adapter will cause the frame discarding. Assert this bit to allow frame discarding. Clear this bit to mask this error.
1     1    CRC_ERROR      RW      This bit signals whether the CRC check error will cause the frame discarding. Assert this bit to allow frame discarding. Clear this bit to mask this error.
2     2    MINTU_CHECK    RW      This bit enables the minimum frame length check. If the incoming frame length is less than the RX MAC LITE minimum frame length register, the frame will be discarded.
3     3    MTU_CHECK      RW      This bit enables the MTU frame length check. If the incoming frame length is greater than the RX MAC LITE frame MTU register, the frame will be discarded.
4     4    MAC_CHECK      RW      This bit enables the frame MAC address check. If the incoming frame destination MAC address doesn't pass the control, the frame will be discarded.
5     31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

**Status register**

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     0    MFIFO_OVF      RW      This bit is asserted in case the MFIFO (frame metadata) overflow has occured. Bit reset is performed by writing operation.
1     1    DFIFO_OVF      RW      This bit is asserted in case the DFIFO (frame data) overflow has occured. Bit reset is performed by writing operation.
2     3    DEBUG          RW      Reserved (tied to zero).
4     6    Obsolete       R       Ignore these bits.
7     7    Link Status    R       Information about the link status (0=no link, 1=link ok).
8     21   Reserved       R       Reserved bits.
22    22   INBANDFCS      R       FCS field removing flag (0 → FCS is removed, 1 → FSC isn't removed).
23    27   MAC_COUNT      R       Number of MAC addresses that can be placed into CAM (at most 16).
28    31   Reserved       R       Reserved bits.
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
- 0x03 - CMD SWITCH ADDRESS SPACE: Switch the output address space (more information here TODO RFC COUNTERS link)

**Minimum frame length allowed**

This register specifies the minimal frame length allowed (MINTU). The frame length includes the length of Ethernet frame including FCS - according to the XGMII specification it is the length of <data> part of XGMII data stream without IFG, preamble, SFD or EFD. Default value is 64.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     15   Min. length    RW      The minimal frame length allowed.
16    31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

**Maximum frame length allowed**

This register specifies the maximal frame length allowed (MTU). The frame length includes the length of Ethernet frame including FCS - according to the XGMII specification it is the length of <data> part of XGMII data stream without IFG, preamble, SFD or EFD. Default value is 64. Default value is 1526.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     15   Max. length    RW      The maximal frame length allowed.
16    31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

**MAC address check mode**

This register specifies the mode of MAC address checking.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     1    Check mode     RW      The MAC address checking mode.
2     31   Reserved       R       Reserved bits.
====  ===  =============  ======  ==============

MAC address checking mode definition:

- 0x00 - MODE 0: All MACs can pass (promiscuous mode).
- 0x01 - MODE 1: Only frames with valid MAC addresses can pass (see MAC memory).
- 0x02 - MODE 2: MODE 1 + All brodcast frames can pass.
- 0x03 - MODE 3: MODE 2 + All multicast frames can pass.

**Octets Received OK Counter - low part (OROCL)**

This is the low part of counter that holds number of data octets in frames that were successfully received. This does not include octets in frames received with MAC, CRC, MINTU, MTU, CRC or CGMII errors according the settings of Error mask register. This counter is incremented when a new packet is successfully received and the length of the currently received packet is added. The counted length of the packets always includes the length of CRC and vice versa.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Octets Received OK Counter - high part (OROCH)**

This is the high part of counter that holds number of data octets in frames that were successfully received. This does not include octets in frames received with MAC, CRC, MINTU, MTU, CRC or CGMII errors according the settings of Error mask register. This counter is incremented when a new packet is successfully received and the length of the currently received packet is added. The counted length of the packets always includes the length of CRC and vice versa.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     31   Counter value  R       Current counter value
====  ===  =============  ======  ==============

**Memory of available MAC addresses**

This memory contains all available MAC addresses for network interface.

====  ===  =============  ======  ==============
From  To   Name           Access  Description
====  ===  =============  ======  ==============
0     47   MAC address    RW      The MAC address.
48    48   Valid bit      RW      MAC address is valid when asserted.
====  ===  =============  ======  ==============

To write the MAC address item properly you must first write low 32 bits and then high 16 bits.
If you would not do it right way the MAC have not been written.
Memory can contains up to 16 MAC addresses (it depends on MAC_COUNT generic).
Each MAC address is stored on two address positions.
The lower address contains the lower 4 bytes and the upper contains the 2 upper bytes and valid bit.
Only valid MAC addresses are used for matching.

.. warning::

    The MAC memory can be accessed by software only when the RX MAC LITE is disabled!

Ports and Generics
^^^^^^^^^^^^^^^^^^

.. vhdl:autoentity:: RX_MAC_LITE
