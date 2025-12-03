-- tx_dma software_manager.vhd: software manager which serves as an interface
-- between MI bus (software side) and the TX DMA system as a whole.
-- Copyright (c) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.dma_bus_pack.all;

-- This component provides a control interface between the TX DMA Calypte controller and the host. The
-- Control/Status (C/S) register address space is initialized for each channel. This component drives the
-- start/stop sequences when requested. When the start/stop of multiple channels is requested, the
-- routine is performed sequentially in a Round-Robin fashion.
entity TX_DMA_SW_MANAGER is
    generic (
        -- Traget device
        DEVICE             : string  := "STRATIX10";

        -- Total number of DMA Channels within this DMA Endpoint
        CHANNELS           : natural := 8;

        -- Actual width of packet and byte counters
        RECV_PKT_CNT_WIDTH : natural := 64;
        RECV_BTS_CNT_WIDTH : natural := 64;
        DISC_PKT_CNT_WIDTH : natural := 64;
        DISC_BTS_CNT_WIDTH : natural := 64;

        -- Width of pointers to data buffers specifying the depth of the
        -- internal buffers in the :ref:`tx_dma_calypte_trans_buffer`.
        DATA_POINTER_WIDTH    : natural := 14;
        -- Width of a virtual DMA header pointer since the buffer is established by a single
        -- FIFO shared among multiple channels. This pointer is to determine the depth of the FIFO.
        DMA_HDR_POINTER_WIDTH : natural := 9;

        -- * Maximum size of a packet (in bytes)
        -- * Defines width of Packet length signals.
        PKT_SIZE_MAX       : natural := 2**12;

        -- Width of MI bus
        MI_WIDTH           : natural := 32
    );
    port (
        CLK                  : in  std_logic;
        RESET                : in  std_logic;

        -- =============================================================================================
        -- MI interface for SW access
        -- =============================================================================================
        MI_ADDR              : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR               : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE                : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD                : in  std_logic;
        MI_WR                : in  std_logic;
        MI_DRD               : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY              : out std_logic;
        MI_DRDY              : out std_logic;

        -- =============================================================================================
        -- Packet counter increment interface
        -- =============================================================================================
        PKT_SENT_CHAN        : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        PKT_SENT_INC         : in  std_logic;
        PKT_SENT_BYTES       : in  std_logic_vector(log2(PKT_SIZE_MAX+1)-1 downto 0);
        PKT_DISCARD_CHAN     : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        PKT_DISCARD_INC      : in  std_logic;
        PKT_DISCARD_BYTES    : in  std_logic_vector(log2(PKT_SIZE_MAX+1)-1 downto 0);

        -- =============================================================================================
        -- Channel status interface
        --
        -- To signal initiation of a start/stop routine to START_STOP_CTRL
        -- =============================================================================================
        START_REQ_CHAN       : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        START_REQ_VLD        : out std_logic;
        START_REQ_ACK        : in  std_logic;

        STOP_REQ_CHAN        : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        STOP_REQ_VLD         : out std_logic;
        STOP_REQ_ACK         : in  std_logic; -- logic request one CLK delay between VLD request and ACK reponse

        -- Mask of active channels
        ENABLED_CHAN         : out std_logic_vector(CHANNELS-1 downto 0);

        -- =========================================================================================
        -- Runtime updates of a pointer within Pointer Updater
        -- =========================================================================================
        RT_UPD_CH      : in  std_logic_vector(log2(CHANNELS) -1 downto 0);
        RT_UPD_BUFF_BA : out std_logic_vector(64 -1 downto 0);
        RT_UPD_P2P_EN  : out std_logic;

        -- =========================================================================================
        -- Stopping/starting a channel within Pointer Updater
        -- =========================================================================================
        PTR_UPD_START_REQ_CH  : out std_logic_vector(log2(CHANNELS) -1 downto 0);
        PTR_UPD_START_REQ_VLD : out std_logic;
        PTR_UPD_START_REQ_ACK : in std_logic;

        PTR_UPD_STOP_REQ_BUFF_BA : out std_logic_vector(64 -1 downto 0);
        PTR_UPD_STOP_REQ_P2P_EN  : out std_logic;
        PTR_UPD_STOP_REQ_HDP     : out std_logic_vector(DATA_POINTER_WIDTH -1 downto 0);
        PTR_UPD_STOP_REQ_HHP     : out std_logic_vector(DMA_HDR_POINTER_WIDTH -1 downto 0);
        PTR_UPD_STOP_REQ_EN      : out std_logic;
        PTR_UPD_STOP_REQ_ACK     : in  std_logic;

        -- =============================================================================================
        -- Pointer update interface
        --
        -- To update pointer values in the C/S registers
        -- =============================================================================================
        HDP_WR_CHAN     : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        HDP_WR_DATA     : in  std_logic_vector(DATA_POINTER_WIDTH-1 downto 0);
        HDP_WR_EN       : in  std_logic;
        HHP_WR_CHAN     : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        HHP_WR_DATA     : in  std_logic_vector(DMA_HDR_POINTER_WIDTH-1 downto 0);
        HHP_WR_EN       : in  std_logic
    );
end entity;

architecture FULL of TX_DMA_SW_MANAGER is

    -- =====================================================================
    --  Constants, aliases, functions
    -- =====================================================================

    -- Width of address for registers within one DMA Channel
    constant REG_ADDR_WIDTH  : natural := 7;

    -- Assigns an index to each register name --
    -- Software Control
    constant R_CONTROL         : natural :=  0;
    -- DMA Channel Status
    constant R_STATUS          : natural :=  1;
    -- Experimental features
    constant R_EXP             : natural :=  2;
    -- Software Descriptor Pointer
    constant R_SDP             : natural :=  4;
    -- Software Header Pointer
    constant R_SHP             : natural :=  5;
    -- Hardware Descriptor Pointer
    constant R_HDP             : natural :=  6;
    -- Hardware Header Pointer
    constant R_HHP             : natural :=  7;
    -- Time in clock cycles when the update of HHP/HDP is repeated
    constant R_UPDATE_TIMEOUT  : natural :=  8;
    -- Base addres of Update Buffer in RAM (bits 31:0)
    constant R_UPD_ADDR_L      : natural := 20;
    -- Base addres of Update Buffer in RAM (bits 63:32)
    constant R_UPD_ADDR_H      : natural := 21;
    -- Mask for SDP and HDP determining Descriptor Buffer size
    constant R_DPM             : natural := 22;
    -- Mask for SHP and HHP determining Header Buffer size
    constant R_HPM             : natural := 23;
    -- Counter for total number of packets sent from the DMA Module (bits 31:0)
    constant R_SENT_PKTS_LOW   : natural := 24;
    -- Counter for total number of packets sent from the DMA Module (bits 63:32)
    constant R_SENT_PKTS_HIGH  : natural := 25;
    -- Counter for total number of bytes sent from the DMA Module (bits 31:0)
    constant R_SENT_BYTES_LOW  : natural := 26;
    -- Counter for total number of bytes sent from the DMA Module (bits 63:32)
    constant R_SENT_BYTES_HIGH : natural := 27;
    -- Counter for total number of packets discarded in the DMA Module (bits 31:0)
    constant R_DISC_PKTS_LOW   : natural := 28;
    -- Counter for total number of packets discarded in the DMA Module (bits 63:32)
    constant R_DISC_PKTS_HIGH  : natural := 29;
    -- Counter for total number of bytes discarded in the DMA Module (bits 31:0)
    constant R_DISC_BYTES_LOW  : natural := 30;
    -- Counter for total number of bytes sdiscarded in the DMA Module (bits 63:32)
    constant R_DISC_BYTES_HIGH : natural := 31;

    -- reserved register numbers
    constant RSV_3  : natural := 3;
    constant RSV_9  : natural := 9;
    constant RSV_10 : natural := 10;
    constant RSV_11 : natural := 11;
    constant RSV_12 : natural := 12;
    constant RSV_13 : natural := 13;
    constant RSV_14 : natural := 14;
    constant RSV_15 : natural := 15;
    constant RSV_16 : natural := 16;
    constant RSV_17 : natural := 17;
    constant RSV_18 : natural := 18;
    constant RSV_19 : natural := 19;

    -- Total number of registers
    constant REGS : natural := 32;

    -- MI address space for each DMA Channel
    constant R_ADDRS : n_array_t(REGS-1 downto 0) := (
    R_CONTROL         => 16#00#,
    R_STATUS          => 16#04#,
    R_EXP             => 16#08#,
    RSV_3             => 16#0C#,
    R_SDP             => 16#10#,
    R_SHP             => 16#14#,
    R_HDP             => 16#18#,
    R_HHP             => 16#1C#,
    R_UPDATE_TIMEOUT  => 16#20#,
    RSV_9             => 16#24#,
    RSV_10            => 16#28#,
    RSV_11            => 16#2C#,
    RSV_12            => 16#30#,
    RSV_13            => 16#34#,
    RSV_14            => 16#38#,
    RSV_15            => 16#3C#,
    RSV_16            => 16#40#,
    RSV_17            => 16#44#,
    RSV_18            => 16#48#,
    RSV_19            => 16#4C#,
    R_UPD_ADDR_L      => 16#50#,
    R_UPD_ADDR_H      => 16#54#,
    R_DPM             => 16#58#,
    R_HPM             => 16#5C#,
    R_SENT_PKTS_LOW   => 16#60#,
    R_SENT_PKTS_HIGH  => 16#64#,
    R_SENT_BYTES_LOW  => 16#68#,
    R_SENT_BYTES_HIGH => 16#6C#,
    R_DISC_PKTS_LOW   => 16#70#,
    R_DISC_PKTS_HIGH  => 16#74#,
    R_DISC_BYTES_LOW  => 16#78#,
    R_DISC_BYTES_HIGH => 16#7C#
    );

    --------

    -- Strobe enable
    -- (set to True for counter registers, which are only updated from counters
    --  by writing 1 from MI and reset by writing 0)
    constant STROBE_EN : b_array_t(REGS-1 downto 0) := (
        R_CONTROL         => FALSE,
        R_STATUS          => FALSE,
        R_EXP             => FALSE,
        RSV_3             => FALSE,
        R_SDP             => FALSE,
        R_SHP             => FALSE,
        R_HDP             => FALSE,
        R_HHP             => FALSE,
        R_UPDATE_TIMEOUT  => FALSE,
        RSV_9             => FALSE,
        RSV_10            => FALSE,
        RSV_11            => FALSE,
        RSV_12            => FALSE,
        RSV_13            => FALSE,
        RSV_14            => FALSE,
        RSV_15            => FALSE,
        RSV_16            => FALSE,
        RSV_17            => FALSE,
        RSV_18            => FALSE,
        RSV_19            => FALSE,
        R_UPD_ADDR_L      => FALSE,
        R_UPD_ADDR_H      => FALSE,
        R_DPM             => FALSE,
        R_HPM             => FALSE,
        R_SENT_PKTS_LOW   => TRUE,
        R_SENT_PKTS_HIGH  => TRUE,
        R_SENT_BYTES_LOW  => TRUE,
        R_SENT_BYTES_HIGH => TRUE,
        R_DISC_PKTS_LOW   => TRUE,
        R_DISC_PKTS_HIGH  => TRUE,
        R_DISC_BYTES_LOW  => TRUE,
        R_DISC_BYTES_HIGH => TRUE
        );

    -- Write enable (set to False for read-only registers)
    -- Must be set to True, when the coresponding index in STROBE_EN is True
    constant WR_EN : b_array_t(REGS-1 downto 0) := (
        R_CONTROL         => TRUE  or STROBE_EN(R_CONTROL        ),
        R_STATUS          => FALSE or STROBE_EN(R_STATUS         ),
        R_EXP             => TRUE  or STROBE_EN(R_EXP            ),
        RSV_3             => FALSE or STROBE_EN(RSV_3            ),
        R_SDP             => TRUE  or STROBE_EN(R_SDP            ),
        R_SHP             => TRUE  or STROBE_EN(R_SHP            ),
        R_HDP             => FALSE or STROBE_EN(R_HDP            ),
        R_HHP             => FALSE or STROBE_EN(R_HHP            ),
        R_UPDATE_TIMEOUT  => TRUE  or STROBE_EN(R_UPDATE_TIMEOUT ),
        RSV_9             => FALSE or STROBE_EN(RSV_9            ),
        RSV_10            => FALSE or STROBE_EN(RSV_10           ),
        RSV_11            => FALSE or STROBE_EN(RSV_11           ),
        RSV_12            => FALSE or STROBE_EN(RSV_12           ),
        RSV_13            => FALSE or STROBE_EN(RSV_13           ),
        RSV_14            => FALSE or STROBE_EN(RSV_14           ),
        RSV_15            => FALSE or STROBE_EN(RSV_15           ),
        RSV_16            => FALSE or STROBE_EN(RSV_16           ),
        RSV_17            => FALSE or STROBE_EN(RSV_17           ),
        RSV_18            => FALSE or STROBE_EN(RSV_18           ),
        RSV_19            => FALSE or STROBE_EN(RSV_19           ),
        R_UPD_ADDR_L      => TRUE  or STROBE_EN(R_UPD_ADDR_L     ),
        R_UPD_ADDR_H      => TRUE  or STROBE_EN(R_UPD_ADDR_H     ),
        R_DPM             => FALSE or STROBE_EN(R_DPM            ),
        R_HPM             => FALSE or STROBE_EN(R_HPM            ),
        R_SENT_PKTS_LOW   => TRUE  or STROBE_EN(R_SENT_PKTS_LOW  ),
        R_SENT_PKTS_HIGH  => TRUE  or STROBE_EN(R_SENT_PKTS_HIGH ),
        R_SENT_BYTES_LOW  => TRUE  or STROBE_EN(R_SENT_BYTES_LOW ),
        R_SENT_BYTES_HIGH => TRUE  or STROBE_EN(R_SENT_BYTES_HIGH),
        R_DISC_PKTS_LOW   => TRUE  or STROBE_EN(R_DISC_PKTS_LOW  ),
        R_DISC_PKTS_HIGH  => TRUE  or STROBE_EN(R_DISC_PKTS_HIGH ),
        R_DISC_BYTES_LOW  => TRUE  or STROBE_EN(R_DISC_BYTES_LOW ),
        R_DISC_BYTES_HIGH => TRUE  or STROBE_EN(R_DISC_BYTES_HIGH)
        );

    -- Actual number of needed write ports for each register
    -- Must be at least 1 for all registers with Write Enable
    constant WR_PORTS : i_array_t(REGS-1 downto 0) := (
        R_CONTROL         => tsel(WR_EN(R_CONTROL        ),1,0) + 1,
        R_STATUS          => tsel(WR_EN(R_STATUS         ),1,0) + 1, -- Channel Start/Stop confirmation
        R_EXP             => tsel(WR_EN(R_EXP            ),1,0) + 0,
        RSV_3             => tsel(WR_EN(RSV_3            ),1,0) + 0,
        R_SDP             => tsel(WR_EN(R_SDP            ),1,0) + 0,
        R_SHP             => tsel(WR_EN(R_SHP            ),1,0) + 0,
        R_HDP             => tsel(WR_EN(R_HDP            ),1,0) + 2, -- Channel Start reset + Start/stop logic of channel core
        R_HHP             => tsel(WR_EN(R_HHP            ),1,0) + 2, -- Channel Start reset + Start/stop logic of channel core
        R_UPDATE_TIMEOUT  => tsel(WR_EN(R_UPDATE_TIMEOUT ),1,0) + 0,
        RSV_9             => tsel(WR_EN(RSV_9            ),1,0) + 0,
        RSV_10            => tsel(WR_EN(RSV_10           ),1,0) + 0,
        RSV_11            => tsel(WR_EN(RSV_11           ),1,0) + 0,
        RSV_12            => tsel(WR_EN(RSV_12           ),1,0) + 0,
        RSV_13            => tsel(WR_EN(RSV_13           ),1,0) + 0,
        RSV_14            => tsel(WR_EN(RSV_14           ),1,0) + 0,
        RSV_15            => tsel(WR_EN(RSV_15           ),1,0) + 0,
        RSV_16            => tsel(WR_EN(RSV_16           ),1,0) + 0,
        RSV_17            => tsel(WR_EN(RSV_17           ),1,0) + 0,
        RSV_18            => tsel(WR_EN(RSV_18           ),1,0) + 0,
        RSV_19            => tsel(WR_EN(RSV_19           ),1,0) + 0,
        R_UPD_ADDR_L      => tsel(WR_EN(R_UPD_ADDR_L     ),1,0) + 0,
        R_UPD_ADDR_H      => tsel(WR_EN(R_UPD_ADDR_H     ),1,0) + 0,
        R_DPM             => tsel(WR_EN(R_DPM            ),1,0) + 0,
        R_HPM             => tsel(WR_EN(R_HPM            ),1,0) + 0,
        R_SENT_PKTS_LOW   => tsel(WR_EN(R_SENT_PKTS_LOW  ),1,0) + 0,
        R_SENT_PKTS_HIGH  => tsel(WR_EN(R_SENT_PKTS_HIGH ),1,0) + 0,
        R_SENT_BYTES_LOW  => tsel(WR_EN(R_SENT_BYTES_LOW ),1,0) + 0,
        R_SENT_BYTES_HIGH => tsel(WR_EN(R_SENT_BYTES_HIGH),1,0) + 0,
        R_DISC_PKTS_LOW   => tsel(WR_EN(R_DISC_PKTS_LOW  ),1,0) + 0,
        R_DISC_PKTS_HIGH  => tsel(WR_EN(R_DISC_PKTS_HIGH ),1,0) + 0,
        R_DISC_BYTES_LOW  => tsel(WR_EN(R_DISC_BYTES_LOW ),1,0) + 0,
        R_DISC_BYTES_HIGH => tsel(WR_EN(R_DISC_BYTES_HIGH),1,0) + 0
        );

    -- Actual number of needed read ports for each register
    -- Must be at least one for all registers because one port is always
    -- dedicated for a read on the MI side
    constant RD_PORTS : i_array_t(REGS-1 downto 0) := (
        R_CONTROL         => 1 + 1,     -- Channel Start/Stop detection
        R_STATUS          => 1 + 1,     -- Channel Start/Stop indication
        R_EXP             => 1 + 2,     -- Channel stop logic + Pointer updater
        RSV_3             => 1 + 0,
        R_SDP             => 1 + 1,     -- Comparator
        R_SHP             => 1 + 1,     -- Comparator
        R_HDP             => 1 + 1,     -- Comparator
        R_HHP             => 1 + 1,     -- Comparator
        R_UPDATE_TIMEOUT  => 1 + 1,     -- Channel stop logic
        RSV_9             => 1 + 0,
        RSV_10            => 1 + 0,
        RSV_11            => 1 + 0,
        RSV_12            => 1 + 0,
        RSV_13            => 1 + 0,
        RSV_14            => 1 + 0,
        RSV_15            => 1 + 0,
        RSV_16            => 1 + 0,
        RSV_17            => 1 + 0,
        RSV_18            => 1 + 0,
        RSV_19            => 1 + 0,
        R_UPD_ADDR_L      => 1 + 2,     -- Channel stop logic + Pointer updater
        R_UPD_ADDR_H      => 1 + 2,     -- Channel stop logic + Pointer updater
        R_DPM             => 1 + 0,
        R_HPM             => 1 + 0,
        R_SENT_PKTS_LOW   => 1 + 0,
        R_SENT_PKTS_HIGH  => 1 + 0,
        R_SENT_BYTES_LOW  => 1 + 0,
        R_SENT_BYTES_HIGH => 1 + 0,
        R_DISC_PKTS_LOW   => 1 + 0,
        R_DISC_PKTS_HIGH  => 1 + 0,
        R_DISC_BYTES_LOW  => 1 + 0,
        R_DISC_BYTES_HIGH => 1 + 0
        );

    -- Write Byte Enable support for each register
    -- Only some registers supports write Byte Enable, since it
    -- means storing the register in mutliple LUTs with independent write ports
    constant WR_BE_SUPPORT : b_array_t(REGS-1 downto 0) := (
        R_CONTROL         => FALSE,
        R_STATUS          => FALSE,
        R_EXP             => FALSE,
        RSV_3             => FALSE,
        R_SDP             => FALSE,
        R_SHP             => FALSE,
        R_HDP             => FALSE,
        R_HHP             => FALSE,
        R_UPDATE_TIMEOUT  => FALSE,
        RSV_9             => FALSE,
        RSV_10            => FALSE,
        RSV_11            => FALSE,
        RSV_12            => FALSE,
        RSV_13            => FALSE,
        RSV_14            => FALSE,
        RSV_15            => FALSE,
        RSV_16            => FALSE,
        RSV_17            => FALSE,
        RSV_18            => FALSE,
        RSV_19            => FALSE,
        R_UPD_ADDR_L      => FALSE,
        R_UPD_ADDR_H      => FALSE,
        R_DPM             => FALSE,
        R_HPM             => FALSE,
        R_SENT_PKTS_LOW   => FALSE,
        R_SENT_PKTS_HIGH  => FALSE,
        R_SENT_BYTES_LOW  => FALSE,
        R_SENT_BYTES_HIGH => FALSE,
        R_DISC_PKTS_LOW   => FALSE,
        R_DISC_PKTS_HIGH  => FALSE,
        R_DISC_BYTES_LOW  => FALSE,
        R_DISC_BYTES_HIGH => FALSE
        );

    -- True width of each register
    -- Only valid bits are propagated from LUTmems, others are forced to '0'.
    constant RD_WIDTH : i_array_t(REGS-1 downto 0) := (
        R_CONTROL         => 1,
        R_STATUS          => 1,
        R_EXP             => 1,
        RSV_3             => 0,
        R_SDP             => DATA_POINTER_WIDTH,
        R_SHP             => DMA_HDR_POINTER_WIDTH,
        R_HDP             => DATA_POINTER_WIDTH,
        R_HHP             => DMA_HDR_POINTER_WIDTH,
        R_UPDATE_TIMEOUT  => MI_WIDTH,
        RSV_9             => 0,
        RSV_10            => 0,
        RSV_11            => 0,
        RSV_12            => 0,
        RSV_13            => 0,
        RSV_14            => 0,
        RSV_15            => 0,
        RSV_16            => 0,
        RSV_17            => 0,
        RSV_18            => 0,
        RSV_19            => 0,
        R_UPD_ADDR_L      => MI_WIDTH,
        R_UPD_ADDR_H      => MI_WIDTH,
        R_DPM             => MI_WIDTH,
        R_HPM             => MI_WIDTH,
        R_SENT_PKTS_LOW   => minimum(MI_WIDTH, RECV_PKT_CNT_WIDTH),
        R_SENT_PKTS_HIGH  => max(0, RECV_PKT_CNT_WIDTH-MI_WIDTH),
        R_SENT_BYTES_LOW  => minimum(MI_WIDTH, RECV_BTS_CNT_WIDTH),
        R_SENT_BYTES_HIGH => max(0, RECV_BTS_CNT_WIDTH-MI_WIDTH),
        R_DISC_PKTS_LOW   => minimum(MI_WIDTH,DISC_PKT_CNT_WIDTH),
        R_DISC_PKTS_HIGH  => max(0,DISC_PKT_CNT_WIDTH-MI_WIDTH),
        R_DISC_BYTES_LOW  => minimum(MI_WIDTH,DISC_BTS_CNT_WIDTH),
        R_DISC_BYTES_HIGH => max(0,DISC_BTS_CNT_WIDTH-MI_WIDTH)
        );

    -- Set TRUE in specific register which have a constant value initialized when design is built
    constant CONST_REGS : b_array_t(REGS-1 downto 0) := (
        R_CONTROL         => FALSE,
        R_STATUS          => FALSE,
        R_EXP             => FALSE,
        RSV_3             => FALSE,
        R_SDP             => FALSE,
        R_SHP             => FALSE,
        R_HDP             => FALSE,
        R_HHP             => FALSE,
        R_UPDATE_TIMEOUT  => FALSE,
        RSV_9             => FALSE,
        RSV_10            => FALSE,
        RSV_11            => FALSE,
        RSV_12            => FALSE,
        RSV_13            => FALSE,
        RSV_14            => FALSE,
        RSV_15            => FALSE,
        RSV_16            => FALSE,
        RSV_17            => FALSE,
        RSV_18            => FALSE,
        RSV_19            => FALSE,
        R_UPD_ADDR_L      => FALSE,
        R_UPD_ADDR_H      => FALSE,
        R_DPM             => TRUE,
        R_HPM             => TRUE,
        R_SENT_PKTS_LOW   => FALSE,
        R_SENT_PKTS_HIGH  => FALSE,
        R_SENT_BYTES_LOW  => FALSE,
        R_SENT_BYTES_HIGH => FALSE,
        R_DISC_PKTS_LOW   => FALSE,
        R_DISC_PKTS_HIGH  => FALSE,
        R_DISC_BYTES_LOW  => FALSE,
        R_DISC_BYTES_HIGH => FALSE
        );

    -- Initializing constant register values
    constant CONST_REG_VALS : slv_array_t(REGS-1 downto 0)(MI_WIDTH -1 downto 0) := (
        R_CONTROL         => (others => '0'),
        R_STATUS          => (others => '0'),
        R_EXP             => (others => '0'),
        RSV_3             => (others => '0'),
        R_SDP             => (others => '0'),
        R_SHP             => (others => '0'),
        R_HDP             => (others => '0'),
        R_HHP             => (others => '0'),
        R_UPDATE_TIMEOUT  => (others => '0'),
        RSV_9             => (others => '0'),
        RSV_10            => (others => '0'),
        RSV_11            => (others => '0'),
        RSV_12            => (others => '0'),
        RSV_13            => (others => '0'),
        RSV_14            => (others => '0'),
        RSV_15            => (others => '0'),
        RSV_16            => (others => '0'),
        RSV_17            => (others => '0'),
        RSV_18            => (others => '0'),
        RSV_19            => (others => '0'),
        R_UPD_ADDR_L      => (others => '0'),
        R_UPD_ADDR_H      => (others => '0'),
        R_DPM             => std_logic_vector(to_unsigned(2**DATA_POINTER_WIDTH -1,MI_WIDTH)),
        R_HPM             => std_logic_vector(to_unsigned(2**DMA_HDR_POINTER_WIDTH -1,MI_WIDTH)),
        R_SENT_PKTS_LOW   => (others => '0'),
        R_SENT_PKTS_HIGH  => (others => '0'),
        R_SENT_BYTES_LOW  => (others => '0'),
        R_SENT_BYTES_HIGH => (others => '0'),
        R_DISC_PKTS_LOW   => (others => '0'),
        R_DISC_PKTS_HIGH  => (others => '0'),
        R_DISC_BYTES_LOW  => (others => '0'),
        R_DISC_BYTES_HIGH => (others => '0')
        );

    -- Maximum number of ports for setting width of signals
    constant WR_PORTS_MAX : natural := max(WR_PORTS);
    constant RD_PORTS_MAX : natural := max(RD_PORTS);

    -- Returns True when given address is an address of a register with STROBE enabled
    function isstrobeaddr (addr : integer) return boolean is
    begin
        for i in 0 to REGS-1 loop
            if (STROBE_EN(i) and R_ADDRS(i) = addr) then
                return true;
            end if;
        end loop;
        return false;
    end function;
    -- =====================================================================

    -- =====================================================================
    --  MI PIPE
    -- =====================================================================
    signal piped_mi_addr : std_logic_vector(MI_WIDTH-1 downto 0);
    signal piped_mi_dwr  : std_logic_vector(MI_WIDTH-1 downto 0);
    signal piped_mi_be   : std_logic_vector(MI_WIDTH/8-1 downto 0);
    signal piped_mi_rd   : std_logic;
    signal piped_mi_wr   : std_logic;
    signal piped_mi_drd  : std_logic_vector(MI_WIDTH-1 downto 0);
    signal piped_mi_ardy : std_logic;
    signal piped_mi_drdy : std_logic;

    signal piped_mi_dwr_reg : std_logic_vector(MI_WIDTH-1 downto 0);
    -- =====================================================================


    -- =====================================================================
    --  MI interface logic
    -- =====================================================================
    signal mi_chan      : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal mi_chani     : integer                                       := 0;
    signal mi_chan_reg  : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal mi_reg_addr  : std_logic_vector(REG_ADDR_WIDTH-1 downto 0);
    signal mi_reg_addri : integer                                       := 0;
    -- =====================================================================


    -- =====================================================================
    --  MI register LUTRAMs
    -- =====================================================================
    signal reg_di      : slv_array_2d_t(REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0);
    signal reg_we      : slv_array_t   (REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0);
    -- writing address
    signal reg_addra   : slv_array_2d_t(REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0)(log2(CHANNELS)-1 downto 0);
    -- reading address
    signal reg_addrb   : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(log2(CHANNELS)-1 downto 0);
    signal reg_dob     : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0);
    signal cntr_do     : slv_array_t   (REGS-1 downto 0)(MI_WIDTH-1 downto 0)                                   := (others => (others => '0'));

    signal reg_dob_opt : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0)          := (others => (others => (others => '0')));
    -- =====================================================================


    -- =====================================================================
    --  Counters logic
    -- =====================================================================
    signal pkt_sent_counter : std_logic_vector(RECV_PKT_CNT_WIDTH-1 downto 0);
    signal bts_sent_counter : std_logic_vector(RECV_BTS_CNT_WIDTH-1 downto 0);
    signal pkt_disc_counter : std_logic_vector(DISC_PKT_CNT_WIDTH-1 downto 0);
    signal bts_disc_counter : std_logic_vector(DISC_BTS_CNT_WIDTH-1 downto 0);

    signal cntr_rst         : std_logic;
    signal cntr_rd          : std_logic;
    signal cntr_rst_reg     : std_logic;
    signal cntr_rd_reg      : std_logic;
    -- =====================================================================


    -- =====================================================================
    --  DMA Channel probing register
    -- =====================================================================
    signal active_chan_reg  : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal active_chan_regu : unsigned        (log2(CHANNELS)-1 downto 0)   := (others => '0'); -- This register has no reset
    signal active_chan_regi : integer                                       := 0;
    -- =====================================================================


    -- =====================================================================
    --  Start request sending
    -- =====================================================================
    type   start_fsm_t is (S_IDLE, S_WAIT_FOR_ST_SP_ACK, S_WAIT_FOR_PTR_UPD_ACK, S_CHANNEL_ENABLE);
    signal start_fsm_pst : start_fsm_t := S_IDLE;
    signal start_fsm_nst : start_fsm_t := S_IDLE;

    signal start_fsm_channel_reg : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal start_fsm_channel     : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal start_acked           : std_logic;
    -- =====================================================================


    -- =====================================================================
    --  Stop request logic
    -- =====================================================================
    type   stop_fsm_type is (
        IDLE, WAIT_FOR_REQ_ACK, DELAY_FOR_DSP_1, DELAY_FOR_DSP_2,
        WAIT_FOR_POINTERS, WAIT_FOR_STATUS_UPDATE, WAIT_FOR_PTR_UPDATE_DISPATCH
    );
    signal stop_fsm_pst : stop_fsm_type;
    signal stop_fsm_nst : stop_fsm_type;

    signal stop_chan_ok         : std_logic;
    signal stop_ptr_ok          : std_logic;
    signal stop_fsm_channel_reg : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal stop_fsm_channel     : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal stop_acked           : std_logic;

    constant UPD_TIMEOUT_CNTR_NULL_VAL : unsigned(MI_WIDTH -1 downto 0) := (others => '0');
    signal   upd_timeout_cntr_reg      : unsigned(MI_WIDTH -1 downto 0);
    signal   upd_timeout_cntr_next     : unsigned(MI_WIDTH -1 downto 0);
    -- =====================================================================


    -- =====================================================================
    --  Enabled channels register array
    -- =====================================================================
    signal enabled_chan_set : std_logic_vector(CHANNELS-1 downto 0);
    signal enabled_chan_rst : std_logic_vector(CHANNELS-1 downto 0);
    -- =====================================================================


    -- =====================================================================
    --  Stop HDP and HHP logic
    -- =====================================================================
    signal comp_hdp_res      : std_logic_vector(1 downto 0);
    signal comp_hpp_res      : std_logic_vector(1 downto 0);
    signal stop_hdp_ok_reg   : std_logic;
    signal stop_hhp_ok_reg   : std_logic;
    -- =====================================================================

    attribute mark_debug : string;

    -- attribute mark_debug of stop_fsm_pst         : signal is "true";
    -- attribute mark_debug of stop_fsm_channel_reg : signal is "true";
    -- attribute mark_debug of stop_chan_ok         : signal is "true";
    -- attribute mark_debug of stop_ptr_ok          : signal is "true";
    -- attribute mark_debug of stop_hdp_ok_reg      : signal is "true";
    -- attribute mark_debug of stop_hhp_ok_reg      : signal is "true";

    -- signal hdp_to_compare : std_logic_vector(DATA_POINTER_WIDTH -1 downto 0);
    -- signal sdp_to_compare : std_logic_vector(DATA_POINTER_WIDTH -1 downto 0);
    -- signal hhp_to_compare : std_logic_vector(DMA_HDR_POINTER_WIDTH -1 downto 0);
    -- signal shp_to_compare : std_logic_vector(DMA_HDR_POINTER_WIDTH -1 downto 0);

    -- attribute mark_debug of hdp_to_compare         : signal is "true";
    -- attribute mark_debug of sdp_to_compare         : signal is "true";
    -- attribute mark_debug of hhp_to_compare         : signal is "true";
    -- attribute mark_debug of shp_to_compare         : signal is "true";

begin

    -- hdp_to_compare <= reg_dob_opt(R_HDP)(1)(DATA_POINTER_WIDTH -1 downto 0);
    -- sdp_to_compare <= reg_dob_opt(R_SDP)(1)(DATA_POINTER_WIDTH -1 downto 0);
    -- hhp_to_compare <= reg_dob_opt(R_HHP)(1)(DMA_HDR_POINTER_WIDTH -1 downto 0);
    -- shp_to_compare <= reg_dob_opt(R_SHP)(1)(DMA_HDR_POINTER_WIDTH -1 downto 0);

    assert (MI_WIDTH = 32)
        report "ERROR: RX DMA Software Manager: MI_WIDTH ("&to_string(MI_WIDTH)&") must be 32b!"
        severity failure;

    -- =====================================================================
    --  MI PIPE
    -- =====================================================================
    -- Added for better timing.

    mi_pipe_i : entity work.MI_PIPE
    generic map (
        DATA_WIDTH => MI_WIDTH,
        ADDR_WIDTH => MI_WIDTH,
        META_WIDTH => 0,
        PIPE_TYPE  => "SHREG",
        USE_OUTREG => TRUE,
        FAKE_PIPE  => FALSE,
        DEVICE     => DEVICE
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        IN_DWR  => MI_DWR,
        IN_MWR  => (others => '0'),
        IN_ADDR => MI_ADDR,
        IN_BE   => MI_BE,
        IN_RD   => MI_RD,
        IN_WR   => MI_WR,
        IN_ARDY => MI_ARDY,
        IN_DRD  => MI_DRD,
        IN_DRDY => MI_DRDY,

        OUT_DWR  => piped_mi_dwr,
        OUT_MWR  => open,
        OUT_ADDR => piped_mi_addr,
        OUT_BE   => piped_mi_be,
        OUT_RD   => piped_mi_rd,
        OUT_WR   => piped_mi_wr,
        OUT_ARDY => piped_mi_ardy,
        OUT_DRD  => piped_mi_drd,
        OUT_DRDY => piped_mi_drdy
    );
    -- =====================================================================


    -- =====================================================================
    --  MI reading interface
    -- =====================================================================
    -- Extract part of MI address which determines destination DMA Channel
    -- the destination DMA channel is specified within bits with the highest order
    mi_chan      <= piped_mi_addr(REG_ADDR_WIDTH+log2(CHANNELS)-1 downto REG_ADDR_WIDTH);
    mi_chani     <= to_integer(unsigned(mi_chan));
    -- Extract part of MI address which determines destination register
    mi_reg_addr  <= piped_mi_addr(REG_ADDR_WIDTH-1 downto 0);
    mi_reg_addri <= to_integer(unsigned(mi_reg_addr));

    mi_chan_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            mi_chan_reg <= mi_chan;
        end if;
    end process;

    -- MI read
    mi_rd_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            piped_mi_drd <= (others => '0');

            if (RESET = '1') then
                piped_mi_drdy <= '0';
            else

                for i in 0 to REGS-1 loop
                    if (mi_reg_addri = R_ADDRS(i)) then
                        piped_mi_drd <= (others => '0');
                        for e in 0 to MI_WIDTH/8-1 loop
                            if (piped_mi_be(e) = '1') then
                                -- preparing data to read in every time
                                -- piped_MI_BE in specified byte euqals 1
                                piped_mi_drd((e+1)*8-1 downto e*8) <= reg_dob_opt(i)(0)((e+1)*8-1 downto e*8);
                            end if;
                        end loop;
                    end if;
                end loop;

                piped_mi_drdy <= piped_mi_rd;

            end if;
        end if;
    end process;

    piped_mi_ardy <= piped_mi_rd or piped_mi_wr;
    -- =====================================================================


    -- =====================================================================
    -- Generation of storage for register values
    -- =====================================================================
    reg_gen : for i in 0 to REGS-1 generate

        -- Generate LUTRAM for non-constant registers
        nonconst_reg_g: if (not CONST_REGS(i)) generate

            -- Generate just one NP_LUTRAM for each MI transaction
            reg_i : entity work.NP_LUTRAM
            generic map (
                DATA_WIDTH  => MI_WIDTH,
                ITEMS       => CHANNELS,
                WRITE_PORTS => WR_PORTS(i),
                READ_PORTS  => RD_PORTS(i),
                DEVICE      => DEVICE
            )
            port map (
                WCLK  => CLK,
                DI    => reg_di   (i)(WR_PORTS(i)-1 downto 0),
                WE    => reg_we   (i)(WR_PORTS(i)-1 downto 0),
                ADDRA => reg_addra(i)(WR_PORTS(i)-1 downto 0),
                ADDRB => reg_addrb(i)(RD_PORTS(i)-1 downto 0),
                DOB   => reg_dob  (i)(RD_PORTS(i)-1 downto 0)
            );

            strobe_gen : if (STROBE_EN(i)) generate

                -- Reset registers by writing 0
                -- Sample registers from counters by writing 1
                -- Reset and sample old value at the same time by writing 2
                with unsigned(piped_mi_dwr_reg) select reg_di (i)(0) <=
                    (others => '0') when to_unsigned(0, MI_WIDTH),
                    cntr_do(i) when others;

                -- reading is performed one clock cycle earlier than the writing
                reg_we   (i)(0) <= '1' when cntr_rd_reg = '1' or cntr_rst_reg = '1' else '0';
                reg_addra(i)(0) <= mi_chan_reg;
                reg_addrb(i)(0) <= mi_chan;

            else generate

                wr_en_gen : if (WR_EN(i)) generate
                    -- Connect MI to the 0th write port of the register
                    reg_di   (i)(0) <= piped_mi_dwr;
                    reg_we   (i)(0) <= '1' when (piped_mi_wr = '1' and mi_reg_addri = R_ADDRS(i)) else '0';
                    reg_addra(i)(0) <= mi_chan;

                end generate;

                -- Connect MI to the 0th read port of the register (reading MI operations)
                reg_addrb(i)(0) <= mi_chan;

            end generate;
            -- Only connect valid output bits
            -- Set others to '0' to enable LUTmem optimalization
            reg_dob_opt_gen : for e in 0 to RD_PORTS(i)-1 generate
                reg_dob_opt(i)(e)(RD_WIDTH(i)-1 downto 0) <= reg_dob(i)(e)(RD_WIDTH(i)-1 downto 0);
            end generate;

        else generate

            -- Connect registers with constant values to the MI, only valid bits
            reg_dob_opt_gen : for e in 0 to RD_PORTS(i)-1 generate
                reg_dob_opt(i)(e)(RD_WIDTH(i) -1 downto 0) <= std_logic_vector(resize(unsigned(CONST_REG_VALS(i)),RD_WIDTH(i)));
            end generate;
        end generate;
    end generate;

    --------
    -- Connect other write interfaces
    -- NON-GENERIC PART OF REGISTERS CODE
    --------
    -- Note: These are all registers which do not have a writing port from
    -- the MI side but there need to be some of them from the internal logic
    -- of the DMA.

    -- Control register -----------------
    reg_di   (R_CONTROL)(1) <= (others => '0');
    reg_we   (R_CONTROL)(1) <= RESET;
    reg_addra(R_CONTROL)(1) <= active_chan_reg;
    ------------------------------------

    -- Status register -----------------
    -- Write '1' when start is detected
    -- Write '0' when acknowledged stop is detected
    reg_di   (R_STATUS)(0) <= (0 => '1', others => '0') when (start_acked = '1' and RESET = '0') else (others => '0');
    reg_we   (R_STATUS)(0) <= start_acked or stop_acked or RESET;
    reg_addra(R_STATUS)(0) <= active_chan_reg;
    ------------------------------------

    -- HDP register --------------------
    -- Reset after DMA Channel Start
    -- Update by Header manager module
    reg_di   (R_HDP)(0) <= (others => '0');
    reg_we   (R_HDP)(0) <= start_acked;
    reg_addra(R_HDP)(0) <= active_chan_reg;

    reg_di   (R_HDP)(1) <= std_logic_vector(resize_left(unsigned(HDP_WR_DATA),MI_WIDTH));
    reg_we   (R_HDP)(1) <= HDP_WR_EN;
    reg_addra(R_HDP)(1) <= HDP_WR_CHAN;
    ------------------------------------

    -- HHP register --------------------
    -- Reset after DMA Channel Start
    -- Update by Header Manager module
    reg_di   (R_HHP)(0) <= (others => '0');
    reg_we   (R_HHP)(0) <= start_acked;
    reg_addra(R_HHP)(0) <= active_chan_reg;

    reg_di   (R_HHP)(1) <= std_logic_vector(resize_left(unsigned(HHP_WR_DATA),MI_WIDTH));
    reg_we   (R_HHP)(1) <= HHP_WR_EN;
    reg_addra(R_HHP)(1) <= HHP_WR_CHAN;
    ------------------------------------
    -- =====================================================================


    -- =====================================================================
    --  Counters logic
    -- =====================================================================
    pkt_sent_cnt_i : entity work.CNT_MULTI_MEMX
    generic map (
        DEVICE        => DEVICE,
        CHANNELS      => CHANNELS,
        CNT_WIDTH     => RECV_PKT_CNT_WIDTH,
        INC_WIDTH     => 1,
        INC_FIFO_SIZE => 512
    )
    port map (
        CLK     => CLK,
        RESET   => RESET,

        INC_CH  => PKT_SENT_CHAN,
        INC_VAL => (others => '1'),
        INC_VLD => PKT_SENT_INC,
        INC_RDY => open, -- If it overflows, it overflows

        RST_CH  => mi_chan,
        RST_VLD => cntr_rst,

        RD_CH   => mi_chan,
        RD_VLD  => cntr_rd,
        RD_VAL  => pkt_sent_counter
    );

    bts_sent_cnt_i : entity work.CNT_MULTI_MEMX
    generic map (
        DEVICE        => DEVICE,
        CHANNELS      => CHANNELS,
        CNT_WIDTH     => RECV_BTS_CNT_WIDTH,
        INC_WIDTH     => log2(PKT_SIZE_MAX+1),
        INC_FIFO_SIZE => 512
    )
    port map (
        CLK     => CLK,
        RESET   => RESET,

        INC_CH  => PKT_SENT_CHAN,
        INC_VAL => PKT_SENT_BYTES,
        INC_VLD => PKT_SENT_INC,
        INC_RDY => open, -- If it overflows, it overflows

        RST_CH  => mi_chan,
        RST_VLD => cntr_rst,

        RD_CH   => mi_chan,
        RD_VLD  => cntr_rd,
        RD_VAL  => bts_sent_counter
    );

    pkt_disc_cnt_i : entity work.CNT_MULTI_MEMX
    generic map (
        DEVICE        => DEVICE,
        CHANNELS      => CHANNELS,
        CNT_WIDTH     => DISC_PKT_CNT_WIDTH,
        INC_WIDTH     => 1,
        INC_FIFO_SIZE => 512
    )
    port map (
        CLK     => CLK,
        RESET   => RESET,

        INC_CH  => PKT_DISCARD_CHAN,
        INC_VAL => (others => '1'),
        INC_VLD => PKT_DISCARD_INC,
        INC_RDY => open, -- If it overflows, it overflows

        RST_CH  => mi_chan,
        RST_VLD => cntr_rst,

        RD_CH   => mi_chan,
        RD_VLD  => cntr_rd,
        RD_VAL  => pkt_disc_counter
    );

    bts_disc_cnt_i : entity work.CNT_MULTI_MEMX
    generic map (
        DEVICE        => DEVICE,
        CHANNELS      => CHANNELS,
        CNT_WIDTH     => DISC_BTS_CNT_WIDTH,
        INC_WIDTH     => log2(PKT_SIZE_MAX+1),
        INC_FIFO_SIZE => 512
    )
    port map (
        CLK     => CLK,
        RESET   => RESET,

        INC_CH  => PKT_DISCARD_CHAN,
        INC_VAL => PKT_DISCARD_BYTES,
        INC_VLD => PKT_DISCARD_INC,
        INC_RDY => open, -- If it overflows, it overflows

        RST_CH  => mi_chan,
        RST_VLD => cntr_rst,

        RD_CH   => mi_chan,
        RD_VLD  => cntr_rd,
        RD_VAL  => bts_disc_counter
    );

    -- Reset when writing value 0 or 2 to any of the Strobing registers
    cntr_rst <= '1' when (piped_mi_wr = '1' and isstrobeaddr(mi_reg_addri) and (unsigned(piped_mi_dwr) = 0 or unsigned(piped_mi_dwr) = 2)) else '0';
    -- Read when writing value 1 or 2 to any of the Strobing registers
    cntr_rd  <= '1' when (piped_mi_wr = '1' and isstrobeaddr(mi_reg_addri) and (unsigned(piped_mi_dwr) = 1 or unsigned(piped_mi_dwr) = 2)) else '0';

    cntr_rstrd_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- when the value 2 is written to the strobing register, than the
            -- reading operation from the register needs to be performed
            -- earlier than the writing operation, necessary delay is provided
            -- by the registers below
            cntr_rst_reg     <= cntr_rst;
            cntr_rd_reg      <= cntr_rd;
            piped_mi_dwr_reg <= piped_mi_dwr;
        end if;
    end process;

    -- Propagate counter values with correct signal width
    cntr_do_pr : process (all)
    begin

        cntr_do <= (others => (others => '0'));

        cntr_do(R_SENT_PKTS_LOW) <= std_logic_vector(resize_left(unsigned(pkt_sent_counter),MI_WIDTH));
        if (RECV_PKT_CNT_WIDTH > MI_WIDTH) then
            cntr_do(R_SENT_PKTS_HIGH) <= std_logic_vector(resize_left(enlarge_right(unsigned(pkt_sent_counter),-MI_WIDTH),MI_WIDTH));
        end if;

        cntr_do(R_SENT_BYTES_LOW) <= std_logic_vector(resize_left(unsigned(bts_sent_counter),MI_WIDTH));
        if (RECV_BTS_CNT_WIDTH > MI_WIDTH) then
            cntr_do(R_SENT_BYTES_HIGH) <= std_logic_vector(resize_left(enlarge_right(unsigned(bts_sent_counter),-MI_WIDTH),MI_WIDTH));
        end if;

        cntr_do(R_DISC_PKTS_LOW) <= std_logic_vector(resize_left(unsigned(pkt_disc_counter),MI_WIDTH));
        if (DISC_PKT_CNT_WIDTH > MI_WIDTH) then
            cntr_do(R_DISC_PKTS_HIGH) <= std_logic_vector(resize_left(enlarge_right(unsigned(pkt_disc_counter),-MI_WIDTH),MI_WIDTH));
        end if;

        cntr_do(R_DISC_BYTES_LOW) <= std_logic_vector(resize_left(unsigned(bts_disc_counter),MI_WIDTH));
        if (DISC_BTS_CNT_WIDTH > MI_WIDTH) then
            cntr_do(R_DISC_BYTES_HIGH) <= std_logic_vector(resize_left(enlarge_right(unsigned(bts_disc_counter),-MI_WIDTH),MI_WIDTH));
        end if;

    end process;
    -- =====================================================================


    -- =====================================================================
    --  DMA Channel probing register
    -- =====================================================================
    -- cycles through all the channels
    active_chan_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            active_chan_regu <= active_chan_regu+1;
        end if;
    end process;

    active_chan_reg  <= std_logic_vector(active_chan_regu);
    active_chan_regi <=       to_integer(active_chan_regu);

    -- reading from registers
    reg_addrb(R_CONTROL)(1) <= active_chan_reg;
    reg_addrb(R_STATUS )(1) <= active_chan_reg;
    -- =====================================================================


    -- =====================================================================
    --  Start request sending
    -- =====================================================================
    start_fsm_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                start_fsm_pst         <= S_IDLE;
                start_fsm_channel_reg <= (others => '0');
            else
                start_fsm_pst         <= start_fsm_nst;
                start_fsm_channel_reg <= start_fsm_channel;
            end if;
        end if;
    end process;

    start_fsm_nst_logic_p : process (all)
    begin
        start_fsm_nst         <= start_fsm_pst;
        start_fsm_channel     <= start_fsm_channel_reg;
        START_REQ_CHAN        <= start_fsm_channel_reg;
        START_REQ_VLD         <= '0';
        start_acked           <= '0';
        enabled_chan_set      <= (others => '0');
        PTR_UPD_START_REQ_CH  <= start_fsm_channel_reg;
        PTR_UPD_START_REQ_VLD <= '0';

        case start_fsm_pst is
            when S_IDLE =>
                if (reg_dob_opt(R_CONTROL)(1)(0) = '1' and reg_dob_opt(R_STATUS)(1)(0) = '0') then
                    start_fsm_nst     <= S_WAIT_FOR_ST_SP_ACK;
                    start_fsm_channel <= active_chan_reg;
                    START_REQ_CHAN    <= active_chan_reg;
                    START_REQ_VLD     <= '1';
                end if;

            when S_WAIT_FOR_ST_SP_ACK =>
                if (START_REQ_ACK = '1') then
                    start_fsm_nst         <= S_WAIT_FOR_PTR_UPD_ACK;
                    PTR_UPD_START_REQ_VLD <= '1';
                end if;

            when S_WAIT_FOR_PTR_UPD_ACK =>
                PTR_UPD_START_REQ_VLD <= '1';

                if (PTR_UPD_START_REQ_ACK = '1') then
                    start_fsm_nst <= S_CHANNEL_ENABLE;
                end if;

            when S_CHANNEL_ENABLE =>
                if (start_fsm_channel = active_chan_reg) then
                    start_fsm_nst                      <= S_IDLE;
                    start_acked                        <= '1';
                    enabled_chan_set(active_chan_regi) <= '1';
                end if;
        end case;
    end process;
    -- =====================================================================


    -- =====================================================================
    --  Stop request logic
    -- =====================================================================
    stop_fsm_pst_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                stop_fsm_pst         <= IDLE;
                stop_fsm_channel_reg <= (others => '0');
                upd_timeout_cntr_reg <= (others => '0');
            else
                stop_fsm_pst         <= stop_fsm_nst;
                stop_fsm_channel_reg <= stop_fsm_channel;
                upd_timeout_cntr_reg <= upd_timeout_cntr_next;
            end if;
        end if;
    end process;

    stop_fsm_nst_logic_p : process (all)
    begin
        stop_fsm_nst          <= stop_fsm_pst;
        stop_fsm_channel      <= stop_fsm_channel_reg;
        STOP_REQ_CHAN         <= stop_fsm_channel_reg;
        STOP_REQ_VLD          <= '0';
        stop_acked            <= '0';
        enabled_chan_rst      <= (others => '0');
        PTR_UPD_STOP_REQ_EN   <= '0';
        upd_timeout_cntr_next <= upd_timeout_cntr_reg;

        case (stop_fsm_pst) is

            when IDLE =>

                if (reg_dob_opt(R_CONTROL)(1)(0) = '0' and reg_dob_opt(R_STATUS)(1)(0) = '1') then
                    stop_fsm_nst     <= WAIT_FOR_PTR_UPDATE_DISPATCH;
                    stop_fsm_channel <= active_chan_reg;
                end if;

            when WAIT_FOR_PTR_UPDATE_DISPATCH =>
                PTR_UPD_STOP_REQ_EN   <= '1';
                upd_timeout_cntr_next <= unsigned(reg_dob_opt(R_UPDATE_TIMEOUT)(1));

                if (PTR_UPD_STOP_REQ_ACK = '1') then
                    stop_fsm_nst <= DELAY_FOR_DSP_1;
                end if;

            when DELAY_FOR_DSP_1 =>

                stop_fsm_nst     <= DELAY_FOR_DSP_2;

            when DELAY_FOR_DSP_2 =>

                stop_fsm_nst     <= WAIT_FOR_POINTERS;

            when WAIT_FOR_POINTERS =>

                -- If timeout is not required, it can be disabled by setting the R_UPDATE_TIMEOUT
                -- register to zero. Only one update dispatch is then performed.
                if (unsigned(reg_dob_opt(R_UPDATE_TIMEOUT)(1)) /= UPD_TIMEOUT_CNTR_NULL_VAL) then
                    if (upd_timeout_cntr_reg /= UPD_TIMEOUT_CNTR_NULL_VAL) then
                        upd_timeout_cntr_next <= upd_timeout_cntr_reg - 1;
                    else
                        -- If timeout runs out, do the pointer update one more time
                        stop_fsm_nst <= WAIT_FOR_PTR_UPDATE_DISPATCH;
                    end if;
                end if;

                if (stop_chan_ok = '1' and stop_ptr_ok = '1') then
                    stop_fsm_nst     <= WAIT_FOR_REQ_ACK;
                    STOP_REQ_VLD     <= '1';
                end if;

            -- wait till Channel core acknowledges the stopping of the channel
            when WAIT_FOR_REQ_ACK =>

                if (STOP_REQ_ACK = '1') then
                    stop_fsm_nst <= WAIT_FOR_STATUS_UPDATE;
                end if;

            when WAIT_FOR_STATUS_UPDATE =>

                if (stop_chan_ok = '1') then
                    stop_fsm_nst                                                 <= IDLE;
                    stop_acked                                                   <= '1';
                    enabled_chan_rst(to_integer(unsigned(stop_fsm_channel_reg))) <= '1';
                end if;
        end case;
    end process;

    -- Detect Stop acknowledgement propagation to Status Register
    stop_chan_ok <= '1' when (stop_fsm_channel_reg = active_chan_reg) else '0';
    stop_ptr_ok  <= stop_hdp_ok_reg and stop_hhp_ok_reg;
    -- =====================================================================


    -- =============================================================================================
    -- Pointer Updater interface for stopping a channel
    -- =============================================================================================
    -- The bit 0 within each channel's R_EXP register enables P2P transfers
    reg_addrb(R_EXP)(1)     <= stop_fsm_channel_reg;
    PTR_UPD_STOP_REQ_P2P_EN <= reg_dob_opt(R_EXP)(1)(0);

    -- Since the signals to the comparator are selected at the same time when pointer values for
    -- pointer updater are needed, the same port is used here.
    PTR_UPD_STOP_REQ_HDP <= reg_dob_opt(R_HDP)(1)(DATA_POINTER_WIDTH-1 downto 0);
    PTR_UPD_STOP_REQ_HHP <= reg_dob_opt(R_HHP)(1)(DMA_HDR_POINTER_WIDTH-1 downto 0);

    reg_addrb(R_UPD_ADDR_L)(1) <= stop_fsm_channel_reg;
    reg_addrb(R_UPD_ADDR_H)(1) <= stop_fsm_channel_reg;
    PTR_UPD_STOP_REQ_BUFF_BA   <= reg_dob_opt(R_UPD_ADDR_H)(1) & reg_dob_opt(R_UPD_ADDR_L)(1);

    reg_addrb(R_UPDATE_TIMEOUT)(1) <= stop_fsm_channel_reg;
    -- =============================================================================================


    -- =============================================================================================
    -- Pointer Updater Interface for runtime pointer updates
    -- =============================================================================================
    reg_addrb(R_UPD_ADDR_L)(2) <= RT_UPD_CH;
    reg_addrb(R_UPD_ADDR_H)(2) <= RT_UPD_CH;
    reg_addrb(R_EXP)(2)        <= RT_UPD_CH;

    tx_rt_upd_data_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            RT_UPD_BUFF_BA <= reg_dob_opt(R_UPD_ADDR_H)(2) & reg_dob_opt(R_UPD_ADDR_L)(2);
            RT_UPD_P2P_EN  <= reg_dob_opt(R_EXP)(2)(0);
        end if;
    end process;
    -- =============================================================================================


    -- =====================================================================
    --  Register array of enabled channels
    -- =====================================================================
    enabled_chan_g : for i in 0 to CHANNELS-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (enabled_chan_set(i) = '1') then
                    ENABLED_CHAN(i) <= '1';
                end if;
                if (enabled_chan_rst(i) = '1' or RESET = '1') then
                    ENABLED_CHAN(i) <= '0';
                end if;
            end if;
        end process;
    end generate;
    -- =====================================================================

    -- =====================================================================
    --  Stop pointer logic
    -- =====================================================================
    reg_addrb(R_HDP)(1) <= stop_fsm_channel_reg;
    reg_addrb(R_HHP)(1) <= stop_fsm_channel_reg;
    reg_addrb(R_SDP)(1) <= stop_fsm_channel_reg;
    reg_addrb(R_SHP)(1) <= stop_fsm_channel_reg;

    -- DSP comparator for HDP
    dsp_comp_hdp_i : entity work.DSP_COMPARATOR
    generic map (
        INPUT_DATA_WIDTH => DATA_POINTER_WIDTH,
        INPUT_REGS_EN    => true,
        DEVICE           => DEVICE,
        MODE             => "><="
    )
    port map (
        CLK      => CLK,
        CLK_EN   => '1',
        RESET    => RESET,

        INPUT_1  => reg_dob_opt(R_HDP)(1)(DATA_POINTER_WIDTH-1 downto 0),
        INPUT_2  => reg_dob_opt(R_SDP)(1)(DATA_POINTER_WIDTH-1 downto 0),

        RESULT   => comp_hdp_res
    );

    stop_hdp_ok_reg <= '1' when (comp_hdp_res = "00") else '0';
    -- =====================================================================


    -- DSP comparator for HHP
    dsp_comp_hhp_i : entity work.DSP_COMPARATOR
    generic map (
        INPUT_DATA_WIDTH => DMA_HDR_POINTER_WIDTH,
        INPUT_REGS_EN    => true,
        DEVICE           => DEVICE,
        MODE             => "><="
    )
    port map (
        CLK      => CLK,
        CLK_EN   => '1',
        RESET    => RESET,

        INPUT_1  => reg_dob_opt(R_HHP)(1)(DMA_HDR_POINTER_WIDTH-1 downto 0),
        INPUT_2  => reg_dob_opt(R_SHP)(1)(DMA_HDR_POINTER_WIDTH-1 downto 0),

        RESULT   => comp_hpp_res
    );

    stop_hhp_ok_reg <= '1' when (comp_hpp_res = "00") else '0';
    -- =====================================================================

end architecture;
