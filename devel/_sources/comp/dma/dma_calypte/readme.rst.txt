.. _dma_calypte:

DMA Calypte
===========

This module allows simple DMA access to the host memory over the PCI Express interface for both,
*Host-to-FPGA (H2F)* and *FPGA-to-Host (F2H)* directions.  The design was primarily focused on the
lowest latency possible.  The module contains two controllers for each direction: the F2H (formerly
named RX) and the H2F (formerly named TX) controller. These allow for the full-duplex transmission
of packet data from/to the host memory. The controllers connect to the surrounding infrastructure
using the :ref:`MFB bus<mfb_bus>`. The packet transmission is part of the Data Flow which is
distinguished from the Control Flow. The Control Flow is established using the :ref:`MI bus<mi_bus>`
that accesses internal Control and Status (C/S) registers. Each of the controllers contains multiple
virtual channels that share the same MFB bus but have separate address spaces in the host memory.
This allows for concurrent access from the host system. The block scheme of the DMA module is
provided in the following figure:

.. figure:: img/tx_calypte_block-dma_whole_alt.svg
    :align: center
    :scale: 150

    The block sheme of the DMA Calypte module and its integration into the NDK
    framework.

.. vhdl:autoentity:: DMA_CALYPTE

.. _dma_calyp_supp_pcie_configs:

Supported PCIe Configurations
-----------------------------

The design can be configured for two major PCIe IP configurations.
This corresponds to setting the input/output MFB bus
interfaces when configuring the DMA_CALYPTE entity.

#. Device: AMD UltraScale+ Architecture, Intel Avalon P-Tile

   PCI Express configuration: **Gen3 x8**

   Internal bus width: 256 bits

   Frequency: 250 MHz

   Input MFB configuration: 1,4,8,8

   Output MFB configuration: 1,1,8,32


#. Device: AMD UltraScale+ architecture, Intel Avalon P-Tile/R-Tile

   PCI Express configuration: **Gen3 x16 (AMD), Gen4 x16 (Intel)**, **Gen5 x8 (Intel)**

   Internal bus width: 512 bits

   Frequency: 250 MHz (AMD), 400 MHz (Intel)

   Input MFB configuration: 1,8,8,8

   Output MFB configuration: 2,1,8,32

Resource consumption
--------------------

The following tables show the resource utilization on the AMD Virtex UltraScale+
chip (``xcvu7p-flvb2104-2-i``) for *Gen3 x8* and *Gen3 x16* PCIe configurations.

+---------------+------------------+---------------+---------------+---------------+
|               | PCIe Gen3 x8                     | PCIe Gen3 x16                 |
+               +------------------+---------------+---------------+---------------+
|               | 16 channels      |64 channels    |16 channels    |64 channels    |
+===============+==================+===============+===============+===============+
| LUT as Logic  | 7650 (0.97%)     | 10441 (1.32%) | 16257 (2.06%) | 18571 (2.36%) |
+---------------+------------------+---------------+---------------+---------------+
| LUT as Memory | 1466 (0.37%)     | 2310 (0.59%)  | 1592 (0.40%)  | 2446 (0.62%)  |
+---------------+------------------+---------------+---------------+---------------+
| Registers     | 10156 (0.64%)    | 11614 (0.74%) | 16290 (1.03%) | 17929 (1.14%) |
+---------------+------------------+---------------+---------------+---------------+
| CARRY logic   | 141 (0.14%)      | 238 (0.24%)   | 145 (0.15%)   | 243 (0.25%)   |
+---------------+------------------+---------------+---------------+---------------+
| RAMB36 Tiles  | 32 (2.22%)       | 128 (8.89%)   | 0 (0.00%)     | 128 (8.89%)   |
+---------------+------------------+---------------+---------------+---------------+
| RAMB18 Tiles  | 8 (0.28%)        | 8 (0.28%)     | 72 (2.50%)    | 8 (0.28%)     |
+---------------+------------------+---------------+---------------+---------------+
| URAMs         | 8 (1.25%)        | 32 (5.00%)    | 8 (1.25%)     | 32 (5.00%)    |
+---------------+------------------+---------------+---------------+---------------+
| DSPs          | 4 (0.09%)        | 4 (0.09%)     | 4 (0.09%)     | 4 (0.09%)     |
+---------------+------------------+---------------+---------------+---------------+

Latency report
--------------

Since this module has been designed for low latency, this is our primary concern. Even though its
RTL design reaches the minimum latency, the PCI Express protocol remains the biggest contributor to
the overall latency. From our observations, the latency is also influenced by the vendor
of the CPU where Intel devices perform slightly better than AMD devices. Some PCIe IPs for FPGAs
provide a special low-latency mode such as the PCIE4 block used in *AMD UltraScale+* architecture, which
is enabled on all AMD cards whose measurements we provide. The latency is always measured as a
*Round-Trip-Time (RTT)* latency either on the path: *Host -> H2F Controller -> FPGA -> F2H Controller
-> Host (HFH)*, or *FPGA -> F2H Controller -> Host -> H2F Controller -> FPGA (FHF)*, which will be
denoted for specific results. Every time the data are looped back, either in the Host for the FHF path
or in the FPGA for the HFH path, the loopback is established with the shortest path possible (E.g., for the
HFH to directly connect *USR_TX_MFB* to the *USR_RX_MFB* interface).

Test case 1 (AMD FPGA)
^^^^^^^^^^^^^^^^^^^^^^

* Card: AMD Alveo X3522PV

  CPU: Intel(R) Xeon(R) E-2226G CPU @ 3.40GHz

  RAM: 64 GB (4 x 16GB)

  PCIe configuration: Gen3x8

* FHF latency (1000 repetitions)

        .. figure:: img/fhf_latency_alveo_x3522pv.jpg
                :align: center
                :scale: 60

* HFH latency (64 byte packets, 1000000 repetitions)

  ~811 ns (median)

  ~1.3 us (0.99-quantile)

Test case 2 (Intel FPGA)
^^^^^^^^^^^^^^^^^^^^^^^^

* Card: Silicom FPGA SmartNIC N6010

  CPU: Intel(R) Xeon(R) Gold 6348 CPU @ 2.60GHz

  RAM: 64 GB (4 x 16GB)

  PCIe configuration: Gen3x8

* FHF latency (1000 repetitions)

        .. figure:: img/latency_n6010_tramin.png
                :align: center
                :height: 450

* HFH latency (64 byte packets, 1000000 repetitions)

  ~1100 ns (median)

  ~1.7 us (0.99-quantile)

Local Subcomponents
-------------------

.. toctree::
   :maxdepth: 1

   comp/rx/readme
   comp/tx/readme

Maintainers
-----------

* Vladislav Valek <valekv@cesnet.cz>
